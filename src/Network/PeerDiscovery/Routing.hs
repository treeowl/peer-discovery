module Network.PeerDiscovery.Routing
  ( initRoutingTable
  , insertPeer
  , unsafeInsertPeer
  , timeoutPeer
  , clearTimeoutPeer
  , findClosest
  ) where

import Data.Functor.Identity
import qualified Data.Foldable as F
import qualified Data.Sequence as S

import Network.PeerDiscovery.Types
import Network.PeerDiscovery.Util

-- | Create empty routing table given our id.
initRoutingTable :: PeerId -> RoutingTable
initRoutingTable peerId =
  RoutingTable { rtId   = peerId
               , rtTree = Bucket S.empty
               }

-- | Insert a peer into the routing table. If a peer with the same identifier,
-- but a different address is already present in the routing table, the existing
-- node info is returned so that we can verify that we're dealing with a
-- legitimate peer rejoining the network after address change, not an adversary
-- trying to impersonate him.
insertPeer :: Config -> Node -> RoutingTable -> Either Node RoutingTable
insertPeer = insertPeerImpl $ \node nodeIdx nodes ->
  let oldNode = S.index nodes nodeIdx
  in if nodePeer (niNode oldNode) == nodePeer (niNode node)
     then Right $ node S.<| S.deleteAt nodeIdx nodes
     else Left  $ niNode oldNode

-- | Unsafely insert a peer into the routing table. If a peer with the same
-- identifier is already present in the routing table, this function will reset
-- his timeout count and update his address. Because of that this function is
-- safe to use only after we verified that the peer is legitimate, i.e. he
-- proved that he possesses the private key corresponding to his
-- identifier. This happens after we sent him a request and received a valid
-- response as all responses are signed by the responder and verified on
-- reception by the sender.
unsafeInsertPeer :: Config -> Node -> RoutingTable -> RoutingTable
unsafeInsertPeer conf peer = runIdentity . insertPeerImpl f conf peer
  where
    f node nodeIdx nodes = Identity $ node S.<| S.deleteAt nodeIdx nodes

-- | Increase the timeout count of a given peer by 1.
timeoutPeer :: Node -> RoutingTable -> RoutingTable
timeoutPeer = modifyTimeoutCount (+1)

-- | Reset the timeout count of a given peer.
clearTimeoutPeer :: Node -> RoutingTable -> RoutingTable
clearTimeoutPeer = modifyTimeoutCount (const 0)

-- | Return up to k peers closest to the target id.
findClosest :: Int -> PeerId -> RoutingTable -> [Node]
findClosest n nid = F.foldr (\node acc -> niNode node : acc) [] . go n 0 . rtTree
  where
    go k !depth = \case
      Bucket nodes     -> S.take k nodes
      Split left right ->
        let bitSet  = testPeerIdBit nid depth
            nodes   = if bitSet
                      then go k (depth + 1) left
                      else go k (depth + 1) right
        in case k - S.length nodes of
          -- If we're missing nodes after picking them from the appropriate
          -- branch, get the rest from the adjacent one.
          missing | missing == 0 -> nodes
                  | otherwise    ->
                    if bitSet
                    then nodes S.>< go missing (depth + 1) right
                    else nodes S.>< go missing (depth + 1) left

----------------------------------------

insertPeerImpl
  :: forall f. Applicative f
  => (NodeInfo -> Int -> S.Seq NodeInfo -> f (S.Seq NodeInfo))
  -> Config
  -> Node
  -> RoutingTable
  -> f RoutingTable
insertPeerImpl updateExistingNode conf peer rt =
  -- We don't want ourselves in the routing table because we are not interested
  -- in "discovering" and talking to ourselves.
  if nodeId peer == rtId rt
  then pure rt
  else go True 0 (rtTree rt) <&> \newTree -> rt { rtTree = newTree }
  where
    node = NodeInfo { niNode         = peer
                    , niTimeoutCount = 0
                    }

    go :: Bool -> Int -> RoutingTree -> f RoutingTree
    go !myBranch !depth = \case
      tree@(Bucket nodes) ->
        case S.findIndexL ((== nodeId peer) . nodeId . niNode) nodes of
          -- If the node is already there, appropriately update it.
          Just nodeIdx -> Bucket <$> updateExistingNode node nodeIdx nodes
          Nothing -> if
            | S.length nodes < configK conf ->
              -- If there is a place in the bucket, simply insert it at the
              -- head.
              pure . Bucket $ node S.<| nodes
            | myBranch || depth `rem` configB conf /= 0 ->
              -- If we are in a branch that represents prefix of our id or the
              -- condition taken from the original Kademlia paper (section 4.2)
              -- is met, split existing bucket into two and recursively select
              -- the appropriate one.
              let (left, right) = S.partition ((`testPeerIdBit` depth) . nodeId . niNode)
                                                nodes
              in go myBranch depth $ Split (Bucket left) (Bucket right)
            | otherwise ->
              -- If the bucket is full and we're at max depth, check if it
              -- contains stale nodes. If so, replace one of them.
              case S.findIndexR ((> configMaxTimeouts conf) . niTimeoutCount) nodes of
                Just nodeIdx -> pure . Bucket $ node S.<| S.deleteAt nodeIdx nodes
                Nothing      -> pure tree
      Split left right ->
        let peerBit = testPeerIdBit (nodeId $ niNode node) depth
            myBit   = testPeerIdBit (rtId rt) depth
            -- Check whether the branch we're going to extends our id prefix.
            nextMyBranch = myBranch && myBit == peerBit
        in if peerBit
        then go nextMyBranch (depth + 1) left  <&> \newLeft  -> Split newLeft right
        else go nextMyBranch (depth + 1) right <&> \newRight -> Split left newRight

modifyTimeoutCount :: (Int -> Int) -> Node -> RoutingTable -> RoutingTable
modifyTimeoutCount modify peer rt = rt { rtTree = go 0 (rtTree rt) }
  where
    go !depth = \case
      tree@(Bucket nodes) ->
        case S.findIndexR ((== peer) . niNode) nodes of
          Just nodeIdx ->
            let f node = node { niTimeoutCount = modify (niTimeoutCount node) }
            in Bucket $ S.adjust' f nodeIdx nodes
          Nothing -> tree
      Split left right ->
        if testPeerIdBit (nodeId peer) depth
        then Split (go (depth + 1) left) right
        else Split left (go (depth + 1) right)
