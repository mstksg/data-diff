{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}

module Data.Diff.Internal (
    Diff(..)
  , Patch(..), DiffLevel(..)
  , compareDiff, noDiff
  , Edit'(..), diff', patch'
  , TuplePatch(..)
  , EitherPatch(..)
  ) where

import           Data.Semigroup hiding (diff)

data DiffLevel = NoDiff
               | PartialDiff
               | TotalDiff
    deriving (Eq, Ord, Show)

instance Semigroup DiffLevel where
    NoDiff      <> NoDiff    = NoDiff
    NoDiff      <> _         = PartialDiff
    PartialDiff <> _         = PartialDiff
    TotalDiff   <> TotalDiff = TotalDiff
    TotalDiff   <> _         = PartialDiff

class Patch a where
    patchLevel :: a -> DiffLevel

class (Eq a, Patch (Edit a)) => Diff a where
    type Edit a
    diff      :: a -> a -> Edit a
    patch     :: Edit a -> a -> Maybe a

newtype Edit' a = Edit' { getEdit' :: Edit a }

diff' :: Diff a => a -> a -> Edit' a
diff' x y = Edit' (diff x y)

patch' :: Diff a => Edit' a -> a -> Maybe a
patch' (Edit' x) = patch x

compareDiff :: Diff a => a -> a -> DiffLevel
compareDiff x y = patchLevel (diff x y)

noDiff :: Diff a => a -> a -> Bool
noDiff x y = compareDiff x y == NoDiff

data TuplePatch a b = TP (Edit a) (Edit b)

instance (Patch (Edit a), Patch (Edit b)) => Patch (TuplePatch a b) where
    patchLevel (TP x y) = patchLevel x <> patchLevel y

instance (Diff a, Diff b) => Diff (a, b) where
    type Edit (a, b)         = TuplePatch a b
    diff (x1, y1) (x2, y2)   = TP (diff x1 x2) (diff y1 y2)
    patch (TP ex ey) (x, y)  = (,) <$> patch ex x <*> patch ey y

data EitherPatch a b = L2L (Edit a)
                     | L2R a b
                     | R2L b a
                     | R2R (Edit b)

instance (Patch (Edit a), Patch (Edit b)) => Patch (EitherPatch a b) where
    patchLevel (L2L e  ) = patchLevel e
    patchLevel (L2R _ _) = TotalDiff
    patchLevel (R2L _ _) = TotalDiff
    patchLevel (R2R e  ) = patchLevel e

instance (Diff a, Diff b) => Diff (Either a b) where
    type Edit (Either a b) = EitherPatch a b
    diff (Left  x) (Left  y) = L2L (diff x y)
    diff (Left  x) (Right y) = L2R x y
    diff (Right x) (Left  y) = R2L x y
    diff (Right x) (Right y) = R2R (diff x y)
    patch (L2L e  ) (Left  x) = Left <$> patch e x
    patch (L2R _ y) (Left  _) = Just (Right y)
    patch (R2L _ x) (Right _) = Just (Left  x)
    patch (R2R e  ) (Right y) = Right <$> patch e y
    patch _         _         = Nothing

