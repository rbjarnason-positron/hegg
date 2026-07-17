{-# LANGUAGE RoleAnnotations #-}

module Data.Equality.Saturation.Rewrites.Internal where

import qualified Data.Map.Lazy as M
import qualified Data.Set as S

import Data.Equality.Graph (ClassId, ENode)
import Data.Equality.Matching (Pattern(..))

-- | An opaque reference to an e-class supplied by a match.
newtype MatchRef scope = MatchRef ClassId
type role MatchRef nominal

matchRefClass :: MatchRef scope -> ClassId
matchRefClass (MatchRef classId) = classId

-- | A right-hand side which may reuse matched e-classes or construct new
-- language nodes.  It cannot request arbitrary merges or run graph actions.
data Rhs scope lang
    = Existing !(MatchRef scope)
    | Fresh !(lang (Rhs scope lang))

-- | Read-only information about one e-class in a match.
data MatchInfo scope analysis lang = MatchInfo
    { matchInfoRef :: !(MatchRef scope)
    , matchInfoAnalysis :: analysis
    , matchInfoNodes :: S.Set (ENode lang)
    }

-- | The root, named variables, and exact non-variable subpatterns captured by
-- one match.
data MatchContext scope analysis lang = MatchContext
    { contextRoot :: !(MatchInfo scope analysis lang)
    , contextBindings
        :: !(M.Map String (MatchInfo scope analysis lang))
    , contextLookupSubtree
        :: Pattern lang -> Maybe (MatchInfo scope analysis lang)
    }

rhsFromPattern
    :: Traversable lang
    => MatchContext scope analysis lang
    -> Pattern lang
    -> Rhs scope lang
rhsFromPattern context pattern'
  | Just matched <- contextLookupSubtree context pattern' =
      Existing $ matchInfoRef matched
rhsFromPattern context (VariablePattern name) =
    case M.lookup name $ contextBindings context of
      Just matched -> Existing $ matchInfoRef matched
      Nothing -> error $ "rewrite: unbound pattern variable " <> show name
rhsFromPattern context (NonVariablePattern node) =
    Fresh $ fmap (rhsFromPattern context) node
