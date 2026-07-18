{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Equality.Saturation.Projection
    ( Projection(..)
    , ProjectionView(..)
    , buildProjectionView
    , validateProjections
    ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Data.Equality.Graph
    ( ClassId
    , EGraph
    , ENode
    , Language
    , children
    , find
    , operator
    )
import Data.Equality.Graph.Internal (memo)
import Data.Equality.Graph.Nodes (foldrWithKeyNM')
import Data.Equality.Matching.Database (Database(..), IntTrie(..))

-- | A directed view from a protected anchor to its definition.
data Projection = Projection
    { projectionAnchor :: !ClassId
    , projectionDefinition :: !ClassId
    }
    deriving (Eq, Ord, Show)

-- | The canonical projection data shared by every rewrite in an iteration.
data ProjectionView lang = ProjectionView
    { projectionDatabase :: !(Database lang)
    , protectedClasses :: !IS.IntSet
    , terminalDefinitions :: !(IM.IntMap ClassId)
    }

buildProjectionView
    :: forall lang analysis
     . Language lang
    => [Projection]
    -> EGraph analysis lang
    -> ProjectionView lang
buildProjectionView requested egraph =
    checked `seq`
      ProjectionView
        { projectionDatabase = database
        , protectedClasses = anchors
        , terminalDefinitions = terminals
        }
  where
    edges = canonicalEdges requested egraph
    checked = checkEdges requested edges
    anchors = IS.fromList $ map fst edges
    childrenByAnchor = IM.fromList edges
    terminals = IM.fromSet terminal anchors

    terminal anchor =
        case IM.lookup anchor childrenByAnchor of
          Nothing -> anchor
          Just definition
            | IS.member definition anchors -> terminal definition
            | otherwise -> definition

    physicalNodes = foldrWithKeyNM' collectNode mempty $ memo egraph
    directNodes = IS.foldr IM.delete physicalNodes anchors
    collectNode node root = IM.insertWith S.union root (S.singleton node)
    reverseEdges =
        IM.fromListWith IS.union
          [ (definition, IS.singleton anchor)
          | (anchor, definition) <- edges
          ]
    visibleNodes = projectionClosure directNodes reverseEdges
    database = IM.foldlWithKey' addClass (DB mempty) visibleNodes
    addClass
        :: Database lang
        -> ClassId
        -> S.Set (ENode lang)
        -> Database lang
    addClass db root = S.foldl' (flip $ insertNode root) db

validateProjections :: [Projection] -> EGraph analysis lang -> ()
validateProjections requested egraph =
    checkEdges requested $ canonicalEdges requested egraph

canonicalEdges
    :: [Projection]
    -> EGraph analysis lang
    -> [(ClassId, ClassId)]
canonicalEdges requested egraph =
    [ (find anchor egraph, find definition egraph)
    | Projection anchor definition <- requested
    ]

checkEdges :: [Projection] -> [(ClassId, ClassId)] -> ()
checkEdges requested edges
  | IS.size anchors /= length requested =
      error "projected saturation: protected anchors were merged or duplicated"
  | any (uncurry (==)) edges =
      error "projected saturation: a protected anchor merged with its definition"
  | hasCycle edges =
      error "projected saturation: projection cycle"
  | otherwise = ()
  where
    anchors = IS.fromList $ map fst edges

hasCycle :: [(ClassId, ClassId)] -> Bool
hasCycle edges =
    fst $ IS.foldl' visitRoot (False, mempty) anchors
  where
    childrenByAnchor = IM.fromList edges
    anchors = IM.keysSet childrenByAnchor

    visitRoot result@(True, _) _ = result
    visitRoot (False, done) root = visit mempty done root

    visit path done root
      | IS.member root path = (True, done)
      | IS.member root done = (False, done)
      | otherwise =
          case IM.lookup root childrenByAnchor of
            Nothing -> (False, IS.insert root done)
            Just child ->
              let (found, done') = visit (IS.insert root path) done child
               in (found, IS.insert root done')

insertNode
    :: Language lang
    => ClassId
    -> ENode lang
    -> Database lang
    -> Database lang
insertNode root node (DB relations) =
    DB $ M.alter (Just . populate (root : children node)) (operator node) relations
  where
    populate [] Nothing = MkIntTrie mempty mempty
    populate (x:xs) Nothing =
        MkIntTrie (IS.singleton x) (IM.singleton x $ populate xs Nothing)
    populate [] (Just trie') = trie'
    populate (x:xs) (Just (MkIntTrie keys children')) =
        MkIntTrie
          (IS.insert x keys)
          (IM.alter (Just . populate xs) x children')

projectionClosure
    :: Ord (lang ClassId)
    => IM.IntMap (S.Set (ENode lang))
    -> IM.IntMap IS.IntSet
    -> IM.IntMap (S.Set (ENode lang))
projectionClosure initial reverseEdges =
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
