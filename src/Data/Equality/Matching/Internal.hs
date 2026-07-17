{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Equality.Matching.Internal
    ( CompiledPattern
    , compilePattern
    , compiledQuery
    , compiledVarsState
    , CaptureSubst
    , captureMatch
    , lookupCapture
    ) where

import Control.Monad (void)
import Data.Foldable (toList)
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M

import Data.Equality.Graph.Classes.Id (ClassId)
import Data.Equality.Graph.Nodes (Operator(..))
import Data.Equality.Language (Language)
import Data.Equality.Matching (Match(..), VarsState, compileToQuery)
import Data.Equality.Matching.Database
    ( Atom(..)
    , ClassIdOrVar(..)
    , Query(..)
    , Var
    , findSubst
    )
import Data.Equality.Matching.Pattern (Pattern(..))

-- | A compiled pattern together with the query variables for each
-- non-variable subpattern occurrence.
data CompiledPattern lang = CompiledPattern
    { compiledQuery :: !(Query lang, Var)
    , compiledVarsState :: !VarsState
    , compiledCaptures :: !(M.Map (PatternKey lang) [Var])
    }

-- | E-class boundaries captured for the non-variable subpatterns of one
-- successful match.
newtype CaptureSubst lang =
    CaptureSubst (M.Map (PatternKey lang) ClassId)

data PatternKey lang
    = PatternVariable !String
    | PatternNode !(Operator lang) ![PatternKey lang]

deriving instance Eq (lang ()) => Eq (PatternKey lang)
deriving instance Ord (lang ()) => Ord (PatternKey lang)

-- | Compile a pattern while retaining its non-variable subpattern roots.
compilePattern :: Language lang => Pattern lang -> CompiledPattern lang
compilePattern pattern' =
    let (query, varsState) = compileToQuery pattern'
        captures =
            M.fromListWith (<>)
              [ (patternKey captured, [var])
              | (captured, var) <- queryCaptures pattern' query
              ]
     in CompiledPattern query varsState captures
{-# INLINABLE compilePattern #-}

queryCaptures
    :: Language lang
    => Pattern lang
    -> (Query lang, Var)
    -> [(Pattern lang, Var)]
queryCaptures (VariablePattern _) (SelectAllQuery queryVar, root)
  | queryVar == root = []
queryCaptures pattern' (Query _ atoms, root) = descend root pattern'
  where
    atomNodes =
        M.fromList
          [ (var, node)
          | Atom (CVar var) node <- atoms
          ]

    descend _ (VariablePattern _) = []
    descend var current@(NonVariablePattern node) =
        case M.lookup var atomNodes of
          Nothing -> error "compilePattern: missing query atom"
          Just queryNode ->
              (current, var)
                : descendChildren (toList node) (toList queryNode)

    descendChildren [] [] = []
    descendChildren (child:children) (queryChild:queryChildren) =
        descendChild child queryChild
          <> descendChildren children queryChildren
    descendChildren _ _ = error "compilePattern: query arity mismatch"

    descendChild (VariablePattern _) (CVar _) = []
    descendChild child@(NonVariablePattern _) (CVar var) = descend var child
    descendChild _ _ = error "compilePattern: literal query variable"
queryCaptures _ _ = error "compilePattern: query does not match pattern"

-- | Resolve the non-variable subpatterns captured by a match.
--
-- A projected database may expose the same syntax at distinct boundaries. A
-- match which assigns those boundaries to repeated occurrences of the same
-- subpattern is ambiguous and is rejected.
captureMatch
    :: Language lang
    => CompiledPattern lang
    -> Match
    -> Maybe (CaptureSubst lang)
captureMatch compiled (Match subst _) =
    CaptureSubst <$> traverse resolveCapture (compiledCaptures compiled)
  where
    resolveCapture vars =
        case IS.toList . IS.fromList $ map (`findSubst` subst) vars of
          [classId] -> Just classId
          _ -> Nothing
{-# INLINABLE captureMatch #-}

-- | Look up an exact non-variable subpattern capture.
lookupCapture
    :: Language lang
    => Pattern lang
    -> CaptureSubst lang
    -> Maybe ClassId
lookupCapture pattern' (CaptureSubst captures) =
    M.lookup (patternKey pattern') captures

patternKey :: Language lang => Pattern lang -> PatternKey lang
patternKey (VariablePattern name) = PatternVariable name
patternKey (NonVariablePattern node) =
    PatternNode (Operator $ void node) $ map patternKey (toList node)
