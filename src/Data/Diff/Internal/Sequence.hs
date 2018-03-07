{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Diff.Internal.Sequence (
    SeqPatch(..)
  , listDiff
  , listPatch
  , seqDiff
  , seqPatch
  , isListDiff
  , isListPatch
  , listDiffBy
  , seqDiffBy
  , isListDiffBy
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Internal
import           Data.Function
import           Data.Semigroup hiding (diff)
import qualified Data.Algorithm.Diff   as D
import qualified Data.Algorithm.Diff3  as D
import qualified Data.List.NonEmpty    as NE
import qualified Data.Semigroup        as S
import qualified Data.Text             as T
import qualified Data.Text.Lazy        as TL
import qualified Data.Vector           as V
import qualified Data.Vector.Primitive as VP
import qualified Data.Vector.Storable  as VS
import qualified Data.Vector.Unboxed   as VU
import qualified GHC.Exts              as E

newtype SeqPatch a = SP { getSP :: [D.Diff a] }
  deriving (Show, Eq)

instance Diff a => Patch (SeqPatch a) where
    patchLevel = maybe NoDiff (sconcat . fmap dLevel)
               . NE.nonEmpty
               . getSP
      where
        dLevel :: D.Diff a -> DiffLevel
        dLevel (D.First _ ) = TotalDiff
        dLevel (D.Second _) = TotalDiff
        dLevel (D.Both x y) = compareDiff x y
    mergePatch (SP es1) (SP es2)
        | xs1 == xs2 = listDiff xs1
                     . concat
                   <$> traverse dehunk (D.diff3By (\x y -> compareDiff x y /= TotalDiff)
                                                  ys xs1 zs
                                       )
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

dehunk
    :: forall a. Diff a
    => D.Hunk a
    -> MergeResult [a]
dehunk = \case
    D.LeftChange  xs     -> NoConflict xs
    D.RightChange ys     -> NoConflict ys
    D.Unchanged   xyzs   -> traverse go xyzs
    D.Conflict    xs _ _ -> Conflict xs
  where
    go :: (a, a, a) -> MergeResult a
    go (x,o,y) = do
        p3 <- mergePatch p1 p2
        maybe Incompatible NoConflict $ patch p3 o
      where
        p1 = diff o x
        p2 = diff o y

listDiffBy
    :: (a -> a -> Bool)
    -> [a]
    -> [a]
    -> SeqPatch a
listDiffBy f xs = SP . D.getDiffBy f xs

listDiff
    :: Diff a
    => [a]
    -> [a]
    -> SeqPatch a
listDiff = listDiffBy $ \x y -> compareDiff x y /= TotalDiff

seqDiffBy
    :: (a -> a -> Bool)
    -> (t -> [a])
    -> t
    -> t
    -> SeqPatch a
seqDiffBy f g = listDiffBy f `on` g

seqDiff
    :: Diff a
    => (t -> [a])
    -> t
    -> t
    -> SeqPatch a
seqDiff = seqDiffBy $ \x y -> compareDiff x y /= TotalDiff

seqPatch
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> SeqPatch a
    -> t
    -> Maybe t
seqPatch f g d = fmap g . listPatch d . f

isListDiffBy
    :: (E.IsList l, Diff (E.Item l))
    => (E.Item l -> E.Item l -> Bool)
    -> l
    -> l
    -> SeqPatch (E.Item l)
isListDiffBy f = seqDiffBy f E.toList


isListDiff
    :: (E.IsList l, Diff (E.Item l))
    => l
    -> l
    -> SeqPatch (E.Item l)
isListDiff = seqDiff E.toList

isListPatch
    :: (E.IsList l, Diff (E.Item l))
    => SeqPatch (E.Item l)
    -> l
    -> Maybe l
isListPatch = seqPatch E.toList E.fromList

listPatch
    :: Eq a
    => SeqPatch a
    -> [a]
    -> Maybe [a]
listPatch (SP es0) = go es0
  where
    go (D.First x  : es) xs = contract x es xs
    go (D.Second x : es) xs = (x :) <$> go es xs
    go (D.Both x y : es) xs = (y :) <$> contract x es xs
    go []                [] = Just []
    go []                _  = Nothing
    contract x es xs = do
      x' : xs' <- pure xs
      guard (x == x')
      go es xs'

instance Diff a => Diff [a] where
    type Edit [a] = SeqPatch a
    diff  = listDiff
    patch = listPatch

instance Diff a => Diff (V.Vector a) where
    type Edit (V.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

instance (Diff a, VS.Storable a) => Diff (VS.Vector a) where
    type Edit (VS.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

instance (Diff a, VU.Unbox a) => Diff (VU.Vector a) where
    type Edit (VU.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

instance (Diff a, VP.Prim a) => Diff (VP.Vector a) where
    type Edit (VP.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

-- | Line-by-line diff
instance Diff T.Text where
    type Edit T.Text = SeqPatch T.Text
    diff  = seqDiffBy (==) (T.splitOn "\n")
    patch = seqPatch       (T.splitOn "\n") (T.intercalate "\n")

-- | Line-by-line diff
instance Diff TL.Text where
    type Edit TL.Text = SeqPatch TL.Text
    diff  = seqDiffBy (==) (TL.splitOn "\n")
    patch = seqPatch       (TL.splitOn "\n") (TL.intercalate "\n")
