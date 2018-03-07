{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Diff.Internal (
    Diff(..)
  , Patch(..), DiffLevel(..), MergeResult(..)
  , merge
  , compareDiff, noDiff
  , Edit'(..), diff', patch'
  , TuplePatch(..)
  , EitherPatch(..)
  , gpatchLevel
  , gmergePatch
  , GPatch(..)
  , gdiff
  , gdiff'
  , gpatch
  , GPatchProd(..)
  , gdiffProd
  , gpatchProd
  ) where

import           Control.Monad
import           Data.Diff.Generics
import           Data.Function
import           Data.Semigroup            (Semigroup(..))
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           GHC.Generics              (Generic)
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Reflection
import qualified GHC.Generics              as G
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
    pure  = return
    (<*>) = ap

instance Monad MergeResult where
    return = NoConflict
    rx >>= f = case rx of
      Incompatible -> Incompatible
      Conflict x   -> case f x of
        Incompatible -> Incompatible
        Conflict y   -> Conflict y
        NoConflict y -> Conflict y
      NoConflict x -> case f x of
        Incompatible -> Incompatible
        Conflict y   -> Conflict y
        NoConflict y -> NoConflict y

class Patch a where
    -- | "Level" of patch
    patchLevel :: a -> DiffLevel
    default patchLevel
        :: (SOP.Generic a, Every (Every Patch) (SOP.Code a))
        => a
        -> DiffLevel
    patchLevel = gpatchLevel

    -- | Left-biased parallel merge of two patches
    --
    -- Returns 'Nothing' if patches come from incompatible sources
    --
    -- Returns 'True' if conflict occurred (and was resolved)
    mergePatch :: a -> a -> MergeResult a
    default mergePatch
        :: (SOP.IsProductType a as, Every Patch as)
        => a
        -> a
        -> MergeResult a
    mergePatch = gmergePatch

class (Eq a, Patch (Edit a)) => Diff a where
    type Edit a
    type instance Edit a = GPatch a
    diff      :: a -> a -> Edit a
    patch     :: Edit a -> a -> Maybe a

    default diff
        :: ( Edit a ~ GPatch a
           , SOP.Generic a
           , Every (Every Diff) (SOP.Code a)
           , Every Typeable (SOP.Code a)
           )
        => a
        -> a
        -> Edit a
    diff = gdiff'

    default patch
        :: ( Edit a ~ GPatch a
           , SOP.Generic a
           , Every (Every Diff) (SOP.Code a)
           )
        => Edit a
        -> a
        -> Maybe a
    patch = gpatch


-- | Left-biased merge of two diffable values.
merge :: Diff a => a -> a -> a -> MergeResult a
merge o x y = do
    pz <- mergePatch px py
    maybe Incompatible NoConflict $ patch pz o
  where
    px = diff o x
    py = diff o y

newtype Edit' a = Edit' { getEdit' :: Edit a }
    deriving (Generic)

instance SOP.Generic (Edit' a)
instance Patch (Edit a) => Patch (Edit' a)

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

-- data Swap a b = Swap a b
--     deriving (Show, Eq, Ord)

-- instance (Eq a, Eq b) => Patch (Swap a b) where
--     patchLevel _   = TotalDiff
--     mergePatch s@(Swap x1 y1) (Swap x2 y2)
--         | x1 == x2  = if y1 == y2
--                         then NoConflict s
--                         else Conflict   s
--         | otherwise = Incompatible

data EitherPatch a b = L2L (Edit a)
                     | L2R b
                     | R2L a
                     | R2R (Edit b)

instance (Patch (Edit a), Patch (Edit b), Eq a, Eq b) => Patch (EitherPatch a b) where
    patchLevel (L2L e) = patchLevel e
    patchLevel (L2R _) = TotalDiff
    patchLevel (R2L _) = TotalDiff
    patchLevel (R2R e) = patchLevel e

    mergePatch   (L2L e1) (L2L e2) = L2L <$> mergePatch e1 e2
    mergePatch   (L2L e1) (L2R _ ) = Conflict (L2L e1)
    mergePatch   (L2L _ ) (R2L _ ) = Incompatible
    mergePatch   (L2L _ ) (R2R _ ) = Incompatible
    mergePatch l@(L2R _ ) (L2L _ ) = Conflict l
    mergePatch l@(L2R _ ) (L2R _ ) = Conflict l
    mergePatch   (L2R _ ) (R2L _ ) = Incompatible
    mergePatch   (L2R _ ) (R2R _ ) = Incompatible
    mergePatch   (R2L _ ) (L2L _ ) = Incompatible
    mergePatch   (R2L _ ) (L2R _ ) = Incompatible
    mergePatch l@(R2L _ ) (R2L _ ) = Conflict l
    mergePatch l@(R2L _ ) (R2R _ ) = Conflict l
    mergePatch   (R2R _ ) (L2L _ ) = Incompatible
    mergePatch   (R2R _ ) (L2R _ ) = Incompatible
    mergePatch l@(R2R _ ) (R2L _ ) = Conflict l
    mergePatch   (R2R e1) (R2R e2) = R2R <$> mergePatch e1 e2

instance (Diff a, Diff b) => Diff (Either a b) where
    type Edit (Either a b) = EitherPatch a b
    diff (Left  x) (Left  y) = L2L (diff x y)
    diff (Left  _) (Right y) = L2R y
    diff (Right _) (Left  y) = R2L y
    diff (Right x) (Right y) = R2R (diff x y)
    patch (L2L e) (Left  x) = Left <$> patch e x
    patch (L2R y) (Left  _) = Just (Right y)
    patch (R2L x) (Right _) = Just (Left  x)
    patch (R2R e) (Right y) = Right <$> patch e y
    patch _       _         = Nothing

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
          Ø                  -> NoDiff
          I x :< Ø           -> patchLevel x
          I x :< xs@(_ :< _) -> patchLevel x <> mergeAll xs

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


newtype GPatch a = GP { getGP :: SumDiff Tuple (Prod Edit') (SOP.Code a) }

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every (Every (Comp Patch Edit')) (SOP.Code a)) => Patch (GPatch a) where
    patchLevel = gpPatchLevel
    mergePatch = gpMergePatch

gpPatchLevel
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> DiffLevel
gpPatchLevel = \case
    GP (SDSame (i :&: j :&: xs))
        | i == j    -> prodPatchLevel xs
                          \\ every @_ @(Every Diff) i
        | otherwise -> TotalDiff <> prodPatchLevel xs
                          \\ every @_ @(Every Diff) i
    GP (SDDiff _ _) -> TotalDiff

prodPatchLevel :: forall as. Every Diff as => Prod Edit' as -> DiffLevel
prodPatchLevel = \case
    Ø                      -> NoDiff
    Edit' x :< Ø           -> patchLevel x
    Edit' x :< xs@(_ :< _) -> patchLevel x <> prodPatchLevel xs

gpMergePatch
    :: (Every (Every (Comp Patch Edit')) (SOP.Code a))
    => GPatch a
    -> GPatch a
    -> MergeResult (GPatch a)
gpMergePatch = \case
    l@(GP (SDSame (i1 :&: j1 :&: es1))) -> \case
      GP (SDSame (i2 :&: j2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl ->
          let k = GP . (\es -> SDSame (i1 :&: j1 :&: es))
                   <$> prodMergePatch es1 es2 \\ every @_ @(Every (Comp Patch Edit')) i1
          in  case testEquality j1 j2 of
                Just Refl -> k
                Nothing   -> Conflict id <*> k
        Nothing -> Incompatible
      GP (SDDiff i2 (_ :&: _)) -> case testEquality i1 i2 of
        Just Refl -> Conflict l
        Nothing   -> Incompatible
    l@(GP (SDDiff i1 (_ :&: _))) -> \case
      GP (SDSame (i2 :&: _ :&: _)) -> case testEquality i1 i2 of
        Just Refl -> Conflict l
        Nothing   -> Incompatible
      GP (SDDiff i2 (_ :&: _)) -> case testEquality i1 i2 of
        Just Refl -> Conflict l
        Nothing   -> Incompatible

prodMergePatch
    :: forall as. Every (Comp Patch Edit') as
    => Prod Edit' as
    -> Prod Edit' as
    -> MergeResult (Prod Edit' as)
prodMergePatch xs = traverse1 G.unComp1 . izipProdWith go xs
  where
    go  :: Index as a
        -> Edit' a
        -> Edit' a
        -> (MergeResult G.:.: Edit') a
    go i x y = G.Comp1 (mergePatch x y) \\ every @_ @(Comp Patch Edit') i

gdiff
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => a
    -> a
    -> GPatch a
gdiff x y = GP $ go x y
  where
    go = diffSOP d `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from
      where
        d :: Index (SOP.Code a) as -> Index as b -> b -> b -> Edit' b
        d i j = diff' \\ every @_ @Diff         j
                      \\ every @_ @(Every Diff) i

gdiff'
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every Typeable (SOP.Code a))
    => a
    -> a
    -> GPatch a
gdiff' x y = GP $ go x y
  where
    go = diffSOP' d `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from
      where
        d :: Index (SOP.Code a) as -> Index as b -> b -> b -> Edit' b
        d i j = diff' \\ every @_ @Diff         j
                      \\ every @_ @(Every Diff) i


gpatch
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> a
    -> Maybe a
gpatch e = fmap (SOP.to . sopSop . map1 (map1 (SOP.I . getI)))
         . patchSOP p (getGP e)
         . map1 (map1 (I . SOP.unI))
         . sopSOP
         . SOP.from
  where
    p :: Index (SOP.Code a) as -> Index as b -> Edit' b -> b -> Maybe b
    p i j = patch' \\ every @_ @Diff         j
                   \\ every @_ @(Every Diff) i

data GPatchProd a = forall as. (SOP.Code a ~ '[as])
                 => GPP { getGPP :: Prod Edit' as }

instance (SOP.IsProductType a as, Every Diff as, Every (Comp Patch Edit') as) => Patch (GPatchProd a) where
    patchLevel (GPP es) = prodPatchLevel es
    mergePatch (GPP es1) (GPP es2) = GPP <$> prodMergePatch es1 es2

gdiffProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => a
    -> a
    -> GPatchProd a
gdiffProd x y = GPP $ go x y
  where
    go :: a -> a -> Prod Edit' as
    go = izipProdWith (\i -> d i `on` SOP.unI) `on`
           sopProd . SOP.unZ . SOP.unSOP . SOP.from
    d :: Index as b -> b -> b -> Edit' b
    d i = diff' \\ every @_ @Diff i

gpatchProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => GPatchProd a
    -> a
    -> Maybe a
gpatchProd (GPP es) =
      fmap (SOP.to . SOP.SOP . SOP.Z . prodSOP)
    . itraverse1 (\i -> fmap SOP.I . go i)
    . zipProd es
    . sopProd
    . SOP.unZ
    . SOP.unSOP
    . SOP.from
  where
    go :: Index as b -> (Edit' :&: SOP.I) b -> Maybe b
    go i (e :&: SOP.I x) = patch' e x \\ every @_ @Diff i

instance (Diff a, Diff b, Diff c) => Diff (a, b, c) where
    type Edit (a,b,c) = GPatchProd (a,b,c)
    diff  = gdiffProd
    patch = gpatchProd

instance (Diff a, Diff b, Diff c, Diff d) => Diff (a, b, c, d) where
    type Edit (a,b,c,d) = GPatchProd (a,b,c,d)
    diff  = gdiffProd
    patch = gpatchProd

instance (Diff a, Diff b, Diff c, Diff d, Diff e) => Diff (a, b, c, d, e) where
    type Edit (a,b,c,d,e) = GPatchProd (a,b,c,d,e)
    diff  = gdiffProd
    patch = gpatchProd

instance (Diff a, Diff b, Diff c, Diff d, Diff e, Diff f) => Diff (a, b, c, d, e, f) where
    type Edit (a,b,c,d,e,f) = GPatchProd (a,b,c,d,e,f)
    diff  = gdiffProd
    patch = gpatchProd

instance (Diff a, Diff b, Diff c, Diff d, Diff e, Diff f, Diff g) => Diff (a, b, c, d, e, f, g) where
    type Edit (a,b,c,d,e,f,g) = GPatchProd (a,b,c,d,e,f,g)
    diff  = gdiffProd
    patch = gpatchProd
