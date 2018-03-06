{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Diff.Sequence (
    listDiff
  , listPatch
  , SeqPatch(..)
  , seqDiff
  , seqPatch
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Internal
import           Data.Function
import           Data.Semigroup
import qualified Data.Algorithm.Diff  as D
import qualified Data.Algorithm.Diff3 as D
import qualified Data.List.NonEmpty   as NE
import qualified Data.Semigroup       as S

newtype SeqPatch a = SP { getSP :: [D.Diff a] }

instance Diff a => Patch (SeqPatch a) where
    patchLevel = maybe NoDiff (sconcat . fmap dLevel)
               . NE.nonEmpty
               . getSP
      where
        dLevel :: D.Diff a -> DiffLevel
        dLevel (D.First _ ) = TotalDiff
        dLevel (D.Second _) = TotalDiff
        dLevel (D.Both x y) = compareDiff x y
    -- WARNING: currently incorrect, Unchanged and diff3 must be made fuzzy
    mergePatch (SP es1) (SP es2)
        | xs1 == xs2 = listDiff xs1
                     . concat
                   <$> traverse dehunk (D.diff3 ys xs1 zs)  -- !!!
        | otherwise  = Incompatible
      where
        (xs1, ys) = recover es1
        (xs2, zs) = recover es2

recover :: forall a. [D.Diff a] -> ([a], [a])
recover = bimap (`appEndo` []) (`appEndo` []) . foldMap go
  where
    go :: D.Diff a -> (Endo [a], Endo [a])
    go = \case
      D.Both   x y -> (S.diff [x], S.diff [y])
      D.First  x   -> (S.diff [x], mempty    )
      D.Second   y -> (mempty    , S.diff [y])

-- WARNING: currently incorrect, Unchanged must be made fuzzy
dehunk
    :: D.Hunk a
    -> MergeResult [a]
dehunk = \case
    D.LeftChange  xs  -> Conflict xs
    D.RightChange ys  -> Conflict ys
    D.Unchanged   xs  -> NoConflict xs      -- !!!
    D.Conflict xs _ _ -> Conflict xs

instance Diff a => Diff [a] where
    type Edit [a] = SeqPatch a
    diff  = listDiff
    patch = listPatch

listDiff
    :: Diff a
    => [a]
    -> [a]
    -> SeqPatch a
listDiff xs = SP . D.getDiffBy noDiff xs

seqDiff
    :: Diff a
    => (t -> [a])
    -> t
    -> t
    -> SeqPatch a
seqDiff f = listDiff `on` f

seqPatch
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> SeqPatch a
    -> t
    -> Maybe t
seqPatch f g d = fmap g . listPatch d . f

listPatch
    :: Eq a
    => SeqPatch a
    -> [a]
    -> Maybe [a]
listPatch (SP es0) = go es0
  where
    go (D.First x  : es) xs = (x :) <$> contract x es xs
    go (D.Second x : es) xs = (x :) <$> go es xs
    go (D.Both x y : es) xs = (y :) <$> contract x es xs
    go []                [] = Just []
    go []                _  = Nothing
    contract x es xs = do
      x' : xs' <- pure xs
      guard (x == x')
      go es xs'
