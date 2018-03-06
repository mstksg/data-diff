{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Diff.Internal (
    Diff(..)
  , Patch(..), DiffLevel(..)
  , compareDiff, noDiff
  , Edit'(..), diff', patch'
  , TuplePatch(..)
  , EitherPatch(..)
  , gpatchLevel
  , gmergePatch
  ) where

import           Data.Function
import           Data.Semigroup            (Semigroup(..))
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           GHC.Generics              (Generic)
import           Type.Class.Higher
import           Type.Class.Witness
import qualified Generics.SOP              as SOP

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

data MergeResult a = Incompatible
                   | Conflict   a
                   | NoConflict a
  deriving (Functor, Show, Eq, Ord)

instance Applicative MergeResult where
    pure = NoConflict
    Incompatible <*> _            = Incompatible
    Conflict _   <*> Incompatible = Incompatible
    Conflict f   <*> Conflict x   = Conflict (f x)
    Conflict f   <*> NoConflict x = Conflict (f x)
    NoConflict _ <*> Incompatible = Incompatible
    NoConflict f <*> Conflict x   = Conflict (f x)
    NoConflict f <*> NoConflict x = NoConflict (f x)

class Patch a where
    -- | "Level" of patch
    patchLevel :: a -> DiffLevel
    -- | Left-biased parallel merge of two patches
    --
    -- Returns 'Nothing' if patches come from incompatible sources
    --
    -- Returns 'True' if conflict occurred (and was resolved)
    mergePatch :: a -> a -> MergeResult a

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
    deriving (Generic)
instance SOP.Generic (TuplePatch a b)

instance (Patch (Edit a), Patch (Edit b)) => Patch (TuplePatch a b) where
    patchLevel = gpatchLevel
    mergePatch = gmergePatch

instance (Diff a, Diff b) => Diff (a, b) where
    type Edit (a, b)         = TuplePatch a b
    diff (x1, y1) (x2, y2)   = TP (diff x1 x2) (diff y1 y2)
    patch (TP ex ey) (x, y)  = (,) <$> patch ex x <*> patch ey y

data EitherPatch a b = L2L (Edit a)
                     | L2R a b
                     | R2L b a
                     | R2R (Edit b)

instance (Patch (Edit a), Patch (Edit b), Eq a, Eq b) => Patch (EitherPatch a b) where
    patchLevel (L2L e  ) = patchLevel e
    patchLevel (L2R _ _) = TotalDiff
    patchLevel (R2L _ _) = TotalDiff
    patchLevel (R2R e  ) = patchLevel e

    mergePatch   (L2L e1   ) (L2L e2   ) = L2L <$> mergePatch e1 e2
    mergePatch   (L2L e1   ) (L2R _  _ ) = Conflict (L2L e1)
    mergePatch   (L2L _    ) (R2L _  _ ) = Incompatible
    mergePatch   (L2L _    ) (R2R _    ) = Incompatible
    mergePatch l@(L2R _  _ ) (L2L _    ) = Conflict l
    mergePatch l@(L2R x1 y1) (L2R x2 y2) = case (x1 == x2, y1 == y2) of
      (True , True ) -> NoConflict l
      (True , False) -> Conflict   l
      (False, _    ) -> Incompatible
    mergePatch   (L2R _  _ ) (R2L _  _ ) = Incompatible
    mergePatch   (L2R _  _ ) (R2R _    ) = Incompatible
    mergePatch   (R2L _  _ ) (L2L _    ) = Incompatible
    mergePatch   (R2L _  _ ) (L2R _  _ ) = Incompatible
    mergePatch l@(R2L y1 x1) (R2L y2 x2) = case (y1 == y2, x1 == x2) of
      (True , True ) -> NoConflict l
      (True , False) -> Conflict   l
      (False, _    ) -> Incompatible
    mergePatch l@(R2L _  _ ) (R2R _    ) = Conflict l
    mergePatch   (R2R _    ) (L2L _    ) = Incompatible
    mergePatch   (R2R _    ) (L2R _  _ ) = Incompatible
    mergePatch l@(R2R _    ) (R2L _  _ ) = Conflict l
    mergePatch   (R2R e1   ) (R2R e2   ) = R2R <$> mergePatch e1 e2

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

gpatchLevel
    :: forall a ass. (SOP.Generic a, SOP.Code a ~ ass, Every (Every Patch) ass)
    => a -> DiffLevel
gpatchLevel = ifromSum go . map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from
  where
    go :: forall as. Index (SOP.Code a) as -> Tuple as -> DiffLevel
    go i = mergeAll \\ every @_ @(Every Patch) i
      where
        mergeAll
            :: Every Patch bs
            => Tuple bs
            -> DiffLevel
        mergeAll = \case
          Ø        -> NoDiff
          I x :< Ø -> patchLevel x

gmergePatch
    :: forall a as. (SOP.IsProductType a as, Every Patch as)
    => a
    -> a
    -> MergeResult a
gmergePatch x0 = fmap (SOP.to . sopSop . InL)
               . traverse1 (fmap SOP.I)
               . go x0
  where
    go :: a -> a -> Prod MergeResult as
    go = izipProdWith (\i (SOP.I x) (SOP.I y) -> mergePatch x y \\ every @_ @Patch i)
      `on` sopProd
         . SOP.unZ
         . SOP.unSOP
         . SOP.from
