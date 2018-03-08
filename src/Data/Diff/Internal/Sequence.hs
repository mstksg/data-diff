{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Data.Diff.Internal.Sequence (
  -- * Diff
    SeqPatch(..)
  , listDiff
  , listPatch
  , seqDiff
  , seqPatch
  , isListDiff
  , isListPatch
  -- * Eq
  , EqSeqPatch(..)
  , eqListDiff
  , eqListPatch
  , eqSeqDiff
  , eqSeqPatch
  , eqIsListDiff
  , eqIsListPatch
  -- * Newtype
  , Lines(..)
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Internal
import           Data.Function
import           Data.Hashable
import           Data.Semigroup hiding (diff)
import           GHC.Generics          (Generic)
import qualified Data.Algorithm.Diff   as D
import qualified Data.Algorithm.Diff3  as D
import qualified Data.HashSet          as HS
import qualified Data.IntSet           as IS
import qualified Data.Semigroup        as S
import qualified Data.Set              as S
import qualified Data.Text             as T
import qualified Data.Text.Lazy        as TL
import qualified Data.Vector           as V
import qualified Data.Vector.Primitive as VP
import qualified Data.Vector.Storable  as VS
import qualified Data.Vector.Unboxed   as VU
import qualified GHC.Exts              as E

newtype SeqPatch a = SP { getSP :: [D.Diff a] }
  deriving (Show, Eq, Generic)

instance Diff a => Patch (SeqPatch a) where
    patchLevel = catLevels . map dLevel . getSP
      where
        dLevel :: D.Diff a -> DiffLevel
        dLevel (D.First _ ) = TotalDiff 1
        dLevel (D.Second _) = TotalDiff 1
        dLevel (D.Both x y) = compareDiff x y
    mergePatch (SP es1) (SP es2)
        | xs1 == xs2 = listDiff xs1
                     . concat
                   <$> traverse dehunk (D.diff3By (\x y -> diffPercent (compareDiff x y) < 0.5)
                                                  ys xs1 zs
                                       )
        | otherwise  = Incompatible
      where
        (xs1, ys) = recover es1
        (xs2, zs) = recover es2

newtype EqSeqPatch a = ESP { getESP :: SeqPatch (EqDiff a) }
  deriving (Show, Eq, Patch, Generic)

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
    D.LeftChange  xs      -> NoConflict xs
    D.RightChange ys      -> NoConflict ys
    D.Unchanged   xyzs    -> traverse go xyzs
    D.Conflict    xs _ ys
      | xs == ys  -> NoConflict xs
      | otherwise -> Conflict xs
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
listDiff = listDiffBy $ \x y -> diffPercent (compareDiff x y) < 0.5

eqListDiff
    :: Eq a
    => [a]
    -> [a]
    -> EqSeqPatch a
eqListDiff x = ESP . listDiff (EqDiff <$> x) . fmap EqDiff

seqDiff
    :: Diff a
    => (t -> [a])
    -> t
    -> t
    -> SeqPatch a
seqDiff f = listDiff `on` f

eqSeqDiff
    :: Eq a
    => (t -> [a])
    -> t
    -> t
    -> EqSeqPatch a
eqSeqDiff f = eqListDiff `on` f

seqPatch
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> SeqPatch a
    -> t
    -> Maybe t
seqPatch f g d = fmap g . listPatch d . f

eqSeqPatch
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> EqSeqPatch a
    -> t
    -> Maybe t
eqSeqPatch f g d = fmap g . eqListPatch d . f

isListDiff
    :: (E.IsList l, Diff (E.Item l))
    => l
    -> l
    -> SeqPatch (E.Item l)
isListDiff = seqDiff E.toList

eqIsListDiff
    :: (E.IsList l, Eq (E.Item l))
    => l
    -> l
    -> EqSeqPatch (E.Item l)
eqIsListDiff = eqSeqDiff E.toList

isListPatch
    :: (E.IsList l, Diff (E.Item l))
    => SeqPatch (E.Item l)
    -> l
    -> Maybe l
isListPatch = seqPatch E.toList E.fromList

eqIsListPatch
    :: (E.IsList l, Eq (E.Item l))
    => EqSeqPatch (E.Item l)
    -> l
    -> Maybe l
eqIsListPatch = eqSeqPatch E.toList E.fromList

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

eqListPatch
    :: Eq a
    => EqSeqPatch a
    -> [a]
    -> Maybe [a]
eqListPatch p = (fmap . map) getEqDiff . listPatch (getESP p) . map EqDiff

-- | Items that aren't completely different are considered modifications,
-- not insertions/deletions.  If this is not desired behavior, map with
-- 'EqDiff'.
instance Diff a => Diff [a] where
    type Edit [a] = SeqPatch a
    diff  = listDiff
    patch = listPatch

-- | See notes for list instance.
instance Diff a => Diff (V.Vector a) where
    type Edit (V.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

-- | See notes for list instance.
instance (Diff a, VS.Storable a) => Diff (VS.Vector a) where
    type Edit (VS.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

-- | See notes for list instance.
instance (Diff a, VU.Unbox a) => Diff (VU.Vector a) where
    type Edit (VU.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

-- | See notes for list instance.
instance (Diff a, VP.Prim a) => Diff (VP.Vector a) where
    type Edit (VP.Vector a) = SeqPatch a
    diff  = isListDiff
    patch = isListPatch

-- | String that is line-by-line diff'd
newtype Lines = Lines { getLines :: String }
    deriving (Show, Eq, Ord, Generic, Read)

-- | Line-by-line diff of 'String's
instance Diff Lines where
    type Edit Lines = EqSeqPatch String
    diff  = eqSeqDiff  (map T.unpack . T.splitOn "\n" . T.pack . getLines)
    patch = eqSeqPatch (map T.unpack . T.splitOn "\n" . T.pack . getLines)
                       (Lines . T.unpack . T.intercalate "\n" . map T.pack)

-- | Line-by-line diff
instance Diff T.Text where
    type Edit T.Text = EqSeqPatch T.Text
    diff  = eqSeqDiff  (T.splitOn "\n")
    patch = eqSeqPatch (T.splitOn "\n") (T.intercalate "\n")

-- | Line-by-line diff
instance Diff TL.Text where
    type Edit TL.Text = EqSeqPatch TL.Text
    diff  = eqSeqDiff  (TL.splitOn "\n")
    patch = eqSeqPatch (TL.splitOn "\n") (TL.intercalate "\n")

-- | Changes are purely inclusion/exclusion
instance Ord a => Diff (S.Set a) where
    type Edit (S.Set a) = EqSeqPatch a
    diff  = eqSeqDiff  S.toList
    patch = eqSeqPatch S.toList S.fromList

-- | Changes are purely inclusion/exclusion
instance Diff IS.IntSet where
    type Edit IS.IntSet = EqSeqPatch Int
    diff  = eqSeqDiff  IS.toList
    patch = eqSeqPatch IS.toList IS.fromList

-- | Changes are purely inclusion/exclusion
instance (Hashable a, Eq a) => Diff (HS.HashSet a) where
    type Edit (HS.HashSet a) = EqSeqPatch a
    diff  = eqSeqDiff  HS.toList
    patch = eqSeqPatch HS.toList HS.fromList
