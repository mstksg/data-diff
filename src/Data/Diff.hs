{-# LANGUAGE TypeFamilies         #-}

module Data.Diff (
    Diff(..)
  , Patch(..), DiffLevel(..), MergeResult(..)
  , merge, compareDiff, noDiff
  , Edit'(..), diff', patch'
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
import           Data.Diff.Generics
import           Data.Diff.Sequence
