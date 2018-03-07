{-# LANGUAGE TypeFamilies         #-}

module Data.Diff (
    Diff(..)
  , Patch(..), DiffLevel(..), MergeResult(..)
  , merge, compareDiff
  , Edit'(..), diff', patch'
  , Swap(..), eqDiff, eqPatch
  , EqDiff(..)
  , TuplePatch(..)
  , EitherPatch(..)
  -- * Generic implementations
  -- ** Patch
  , gpatchLevel
  , gmergePatch
  -- ** Diff
  -- *** Sequences
  , listDiff
  , listPatch
  , SeqPatch(..)
  , seqDiff
  , seqPatch
  -- *** Generic ADTs
  , GPatch(..)
  , gdiff
  , gdiff'
  , gpatch
  , GPatchProd(..)
  , gdiffProd
  , gpatchProd
  , SumDiff(..)
  ) where

import           Data.Diff.Internal
import           Data.Diff.Internal.Generics
import           Data.Diff.Internal.Sequence
