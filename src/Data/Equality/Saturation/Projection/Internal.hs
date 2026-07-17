{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Equality.Saturation.Projection.Internal
    ( MatchingView(..)
    , ordinaryMatchingView
    , projectedMatchingView
    ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Data.Equality.Graph
    ( EClass(..)
    , EGraph
    , ENode(..)
    , Language
    , children
    , find
    , operator
    )
import Data.Equality.Graph.Internal (classes, memo)
import Data.Equality.Graph.Nodes (foldrWithKeyNM')
import Data.Equality.Matching (eGraphToDatabase)
import Data.Equality.Matching.Database (Database(..), IntTrie(..))
import Data.Equality.Saturation.Projection

-- | The per-iteration relational view shared by all rewrites.
data MatchingView lang = MatchingView
    { matchingDatabase :: !(Database lang)
    , protectedClasses :: !IS.IntSet
    , protectedEdges :: ![(Int, Int)]
    , visibleNodes :: !(IM.IntMap (S.Set (ENode lang)))
    }

ordinaryMatchingView :: Language lang => EGraph a lang -> MatchingView lang
ordinaryMatchingView egraph =
    MatchingView
      { matchingDatabase = eGraphToDatabase egraph
      , protectedClasses = mempty
      , protectedEdges = []
      , visibleNodes =
          IM.map eClassNodes $ classes egraph
      }

-- | Build a matching database which looks through projection nodes.
--
-- An ordinary row @R_f(child, ...)@ is copied to every class which projects to
-- @child@, with only the row root changed.  Its real children are retained, so
-- nested matching follows the same view recursively.
projectedMatchingView
    :: forall key lang analysis
     . (Ord key, Language lang)
    => ProjectionView key lang
    -> EGraph analysis lang
    -> MatchingView lang
projectedMatchingView projectionView egraph
    | any isSelfProtected projections =
        error "projected saturation: a protected projection points to itself"
    | hasDuplicateKeys protected =
        error "projected saturation: duplicate protected projection key"
    | length protected /= IS.size protectedRoots =
        error "projected saturation: protected projection classes were merged"
    | not . IS.null $ protectedRoots `IS.intersection` transparentRoots =
        error "projected saturation: a protected class also contains an alias"
    | hasProtectedCycle projections =
        error "projected saturation: protected projection cycle"
    | otherwise =
        MatchingView
          { matchingDatabase = database
          , protectedClasses = protectedRoots
          , protectedEdges =
              [(root, child) | (Just _, root, child) <- projections]
          , visibleNodes = closure
          }
  where
    (directNodes, projections, protected) =
        foldrWithKeyNM' collectNode (mempty, [], []) (memo egraph)

    collectNode
        :: ENode lang
        -> Int
        -> ( IM.IntMap (S.Set (ENode lang))
           , [(Maybe key, Int, Int)]
           , [(key, Int)]
           )
        -> ( IM.IntMap (S.Set (ENode lang))
           , [(Maybe key, Int, Int)]
           , [(key, Int)]
           )
    collectNode node@(Node languageNode) root (nodes, edges, keys) =
        case classifyProjection projectionView languageNode of
          Nothing ->
              (IM.insertWith S.union root (S.singleton node) nodes, edges, keys)
          Just (ProtectedProjection key child) ->
              ( nodes
              , (Just key, root, find child egraph) : edges
              , (key, root) : keys
              )
          Just (TransparentProjection child) ->
              (nodes, (Nothing, root, find child egraph) : edges, keys)

    protectedRoots = IS.fromList $ map snd protected
    transparentRoots =
        IS.fromList [root | (Nothing, root, _) <- projections]
    reverseEdges =
        IM.fromListWith IS.union
          [ (child, IS.singleton root)
          | (_, root, child) <- projections
          ]
    closure = transparentClosure directNodes reverseEdges
    database =
        IM.foldlWithKey' addVisibleClass (DB mempty) closure

    addVisibleClass
        :: Database lang
        -> Int
        -> S.Set (ENode lang)
        -> Database lang
    addVisibleClass db root =
        S.foldl' (flip $ insertVisibleNode root) db

    isSelfProtected (Just _, root, child) = root == child
    isSelfProtected _ = False

insertVisibleNode
    :: Language lang
    => Int
    -> ENode lang
    -> Database lang
    -> Database lang
insertVisibleNode root node (DB relations) =
    DB $ M.alter (Just . populate (root : children node))
                 (operator node)
                 relations
  where
    populate [] Nothing = MkIntTrie mempty mempty
    populate (x:xs) Nothing =
        MkIntTrie (IS.singleton x) (IM.singleton x $ populate xs Nothing)
    populate [] (Just trie') = trie'
    populate (x:xs) (Just (MkIntTrie keys children')) =
        MkIntTrie
          (IS.insert x keys)
          (IM.alter (Just . populate xs) x children')

hasDuplicateKeys :: Ord key => [(key, Int)] -> Bool
hasDuplicateKeys = any ((> 1) . length) . M.elems
                 . M.fromListWith (<>) . map (\(key, root) -> (key, [root]))

-- Transparent aliases may legitimately be merged back into a class reached by
-- a protected projection.  Their closure is finite, so only cycles made solely
-- from protected edges are rejected.
hasProtectedCycle :: [(Maybe key, Int, Int)] -> Bool
hasProtectedCycle projections =
    fst $ IS.foldl' visitRoot (False, mempty) (IM.keysSet protectedChildren)
  where
    protectedChildren =
        IM.fromListWith IS.union
          [ (root, IS.singleton child)
          | (Just _, root, child) <- projections
          ]
    visitRoot result@(True, _) _ = result
    visitRoot (False, done) root = visit mempty done root

    visit path done root
      | IS.member root path = (True, done)
      | IS.member root done = (False, done)
      | otherwise =
          let path' = IS.insert root path
              (found, done') =
                  IS.foldl'
                    (visitChild path')
                    (False, done)
                    (IM.findWithDefault mempty root protectedChildren)
           in (found, IS.insert root done')

    visitChild _ result@(True, _) _ = result
    visitChild path (False, done) child = visit path done child

transparentClosure
    :: Ord (lang Int)
    => IM.IntMap (S.Set (ENode lang))
    -> IM.IntMap IS.IntSet
    -> IM.IntMap (S.Set (ENode lang))
transparentClosure initial reverseEdges =
    go initial (Seq.fromList $ IM.keys initial) (IM.keysSet initial)
  where
    go !nodes Seq.Empty _ = nodes
    go !nodes (child Seq.:<| queue) queued =
        let queued' = IS.delete child queued
            childNodes = IM.findWithDefault mempty child nodes
            parents = IM.findWithDefault mempty child reverseEdges
            (nodes', queue', queued'') =
                IS.foldl'
                  (propagate childNodes)
                  (nodes, queue, queued')
                  parents
         in go nodes' queue' queued''

    propagate childNodes (nodes, queue, queued) parent =
        let oldNodes = IM.findWithDefault mempty parent nodes
            newNodes = oldNodes <> childNodes
         in if S.size oldNodes == S.size newNodes
              then (nodes, queue, queued)
              else
                ( IM.insert parent newNodes nodes
                , if IS.member parent queued
                    then queue
                    else queue Seq.|> parent
                , IS.insert parent queued
                )
