{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies    #-}

module Data.Diff (
    Diff(..)
  , Patch(..), DiffLevel(..), MergeResult(..)
  , merge, catLevels, normDL, dlPercent, percentDiff, prodPatchLevel
  , compareDiff
  , ShowPatch(..)
  , DefaultDiff(..)
  , Edit'(..), diff', patch', undiff'
  , Swap(..), eqDiff, eqPatch
  , EqDiff(..)
  -- * Generic implementations
  -- ** Patch
  , gpatchLevel
  , gmergePatch
  -- ** Diff
  -- *** Sequences
  -- **** Diff
  , SeqPatchAt(..)
  , SeqPatch
  , listDiff
  , listPatch
  , listUndiff
  , seqDiff
  , seqPatch
  , seqUndiff
  -- **** Eq
  , EqSeqPatch(..)
  , eqListDiff
  , eqListPatch
  , eqListUndiff
  , eqSeqDiff
  , eqSeqPatch
  , eqSeqUndiff
  -- **** Line-by-line
  , LinesPatch(..)
  , Lines(..)
  -- *** Generic ADTs
  , GPatch(..)
  , gdiff
  , gdiff'
  , gpatch
  , gundiff
  , GPatchProd(..)
  , gdiffProd
  , gpatchProd
  , gundiffProd
  , SumDiff(..)
  , CtrDiff(..)
  -- ** Maps
  , ValDiff(..)
  , MapDiff(..)
  ) where

import           Data.Diff.Internal
import           Data.Diff.Internal.Generics
import           Data.Diff.Internal.Map
import           Data.Diff.Internal.Sequence
