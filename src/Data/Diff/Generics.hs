{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}


module Data.Diff.Generics (
    GPatch(..)
  , gdiff
  , gdiff'
  , gpatch
  , GPatchProd(..)
  , gdiffProd
  , gpatchProd
  , SumDiff(..)
  ) where

import           Data.Diff.Internal
import           Data.Function
import           Data.Kind
import           Data.Semigroup            ((<>))
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Reflection
import qualified Data.Type.Sum             as TCS
import qualified Generics.SOP              as SOP

newtype GPatch a = GP { getGP :: SumDiff Tuple (Prod Edit') (SOP.Code a) }

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a)) => Patch (GPatch a) where
    patchLevel = gpPatchLevel

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
    Ø                  -> NoDiff
    Edit' x :< Ø       -> patchLevel x
    Edit' x :< y :< zs -> patchLevel x <> prodPatchLevel (y :< zs)

gdiff
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => a
    -> a
    -> GPatch a
gdiff x y = GP $ go x y
  where
    go = diffSOP `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from

gdiff'
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every Typeable (SOP.Code a))
    => a
    -> a
    -> GPatch a
gdiff' x y = GP $ go x y
  where
    go = diffSOP' `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from


gpatch
    :: (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> a
    -> Maybe a
gpatch e = fmap (SOP.to . sopSop . map1 (map1 (SOP.I . getI)))
         . patchSOP (getGP e)
         . map1 (map1 (I . SOP.unI))
         . sopSOP
         . SOP.from

data GPatchProd a = forall as. (SOP.Code a ~ '[as])
                 => GPP { getGPP :: Prod Edit' as }

instance (SOP.IsProductType a as, Every Diff as) => Patch (GPatchProd a) where
    patchLevel (GPP es) = prodPatchLevel es

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

data SumDiff :: (k -> Type) -> (k -> Type) -> [k] -> Type where
    SDSame :: (Index as :&: Index as :&: g) a -> SumDiff f g as
    SDDiff :: (Index as :&: f) a -> (Index as :&: f) b -> SumDiff f g as

sumDiff
    :: forall f g as. ()
    => (forall a. (Index as :&: f :&: f) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
    case testEquality i j of
      Just Refl -> SDSame (i :&: i :&: f (i :&: x :&: y))
      Nothing   -> SDDiff (i :&: x) (j :&: y)

-- | Version of sumDiff that uses 'SDSame' if two different indices, but
-- same type
sumDiff'
    :: forall f g as. Every Typeable as
    => (forall a. Typeable a => ((Index as :&: f) :&: (Index as :&: f)) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff' f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
        every @_ @Typeable i //
        every @_ @Typeable j //
    case testEquality (tr i) (tr j) of
      Just Refl -> SDSame (i :&: j :&: f ((i :&: x) :&: (j :&: y)))
      Nothing   -> SDDiff (i :&: x) (j :&: y)
  where
    tr :: Typeable a => p a -> TypeRep a
    tr _ = typeRep

diffSOP
    :: forall ass. Every (Every Diff) ass
    => Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod Edit') ass
diffSOP = sumDiff combine
  where
    combine
        :: forall as. ()
        => (Index ass :&: Tuple :&: Tuple) as
        -> Prod Edit' as
    combine (i :&: xs :&: ys) = every @_ @(Every Diff) i //
        izipProdWith go xs ys
      where
        go :: Every Diff as => Index as a -> I a -> I a -> Edit' a
        go j (I x) (I y) = diff' x y \\ every @_ @Diff j

diffSOP'
    :: forall ass. (Every (Every Diff) ass, Every Typeable ass)
    => Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod Edit') ass
diffSOP' = sumDiff' combine
  where
    combine
        :: forall as. ()
        => ((Index ass :&: Tuple) :&: (Index ass :&: Tuple)) as
        -> Prod Edit' as
    combine ((i :&: xs) :&: (_ :&: ys)) = every @_ @(Every Diff) i //
        izipProdWith go xs ys
      where
        go :: Every Diff as => Index as a -> I a -> I a -> Edit' a
        go j (I x) (I y) = diff' x y \\ every @_ @Diff j

patchSOP
    :: forall ass. Every (Every Diff) ass
    => SumDiff Tuple (Prod Edit') ass
    -> Sum Tuple ass
    -> Maybe (Sum Tuple ass)
patchSOP = \case
    SDSame (i :&: j :&: es) -> \xss -> every @_ @(Every Diff) i // do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go k) (zipProd es xs)
      return (injectSum j ys)
    SDDiff (i :&: _) (j :&: ys) -> \xss -> do
      _  <- TCS.index i xss
      return (injectSum j ys)
  where
    go  :: Every Diff as => Index as a -> (Edit' :&: I) a -> Maybe a
    go k (e :&: I x) = patch' e x \\ every @_ @Diff k
