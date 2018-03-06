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
import           Type.Family.Constraint
import           Type.Reflection
import qualified Data.Type.Sum             as TCS
import qualified GHC.Generics              as G
import qualified Generics.SOP              as SOP

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

data SumDiff :: (k -> Type) -> (k -> Type) -> [k] -> Type where
    SDSame :: (Index as :&: Index as :&: g) a -> SumDiff f g as
    SDDiff :: Index as a -> (Index as :&: f) b -> SumDiff f g as

sumDiff
    :: forall f g as. ()
    => (forall a. (Index as :&: f :&: f) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
    case testEquality i j of
      Just Refl -> SDSame (i :&: i :&: f (i :&: x :&: y))
      Nothing   -> SDDiff i (j :&: y)

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
      Nothing   -> SDDiff i (j :&: y)
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
    SDDiff i (j :&: ys) -> \xss -> do
      _  <- TCS.index i xss
      return (injectSum j ys)
  where
    go  :: Every Diff as => Index as a -> (Edit' :&: I) a -> Maybe a
    go k (e :&: I x) = patch' e x \\ every @_ @Diff k
