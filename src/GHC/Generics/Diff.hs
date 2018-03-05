{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}


module GHC.Generics.Diff (
    GDiff(..)
  , gdiff
  , gdiff'
  , gpatch
  , GDiffProd(..)
  , gdiffProd
  , gpatchProd
  , SumDiff(..)
  ) where

import           Data.Diff
import           Data.Function
import           Data.Kind
import           Data.Singletons.Decide
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Reflection
import qualified Data.Type.Product      as TCP
import qualified Data.Type.Sum          as TCS
import qualified Generics.SOP           as SOP

newtype GDiff a ass = GDiff { getGDiff :: SumDiff Tuple (Prod Edit') ass }

gdiff
    :: forall a ass. (SOP.Generic a, SOP.Code a ~ ass, Every (Every Diff) ass)
    => a
    -> a
    -> GDiff a ass
gdiff x y = GDiff $ go x y
  where
    go = diffSOP `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from

gdiff'
    :: forall a ass. (SOP.Generic a, SOP.Code a ~ ass, Every (Every Diff) ass, Every Typeable ass)
    => a
    -> a
    -> GDiff a ass
gdiff' x y = GDiff $ go x y
  where
    go = diffSOP' `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from


gpatch
    :: (SOP.Generic a, SOP.Code a ~ ass, Every (Every Diff) ass)
    => GDiff a ass
    -> a
    -> Maybe a
gpatch e = fmap (SOP.to . sopSop . map1 (map1 (SOP.I . getI)))
         . patchSOP (getGDiff e)
         . map1 (map1 (I . SOP.unI))
         . sopSOP
         . SOP.from

newtype GDiffProd a as = GDiffProd { getGDiffProd :: Prod Edit' as }

gdiffProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => a
    -> a
    -> GDiffProd a as
gdiffProd x y = GDiffProd $ go x y
  where
    go :: a -> a -> Prod Edit' as
    go = izipProdWith (\i -> d i `on` SOP.unI) `on`
           sopProd . SOP.unZ . SOP.unSOP . SOP.from
    d :: Index as b -> b -> b -> Edit' b
    d i = diff' \\ every @_ @Diff i

gpatchProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => GDiffProd a as
    -> a
    -> Maybe a
gpatchProd es = fmap (SOP.to . SOP.SOP . SOP.Z . prodSOP)
              . itraverse1 (\i -> fmap SOP.I . go i)
              . zipProd (getGDiffProd es)
              . sopProd
              . SOP.unZ
              . SOP.unSOP
              . SOP.from
  where
    go :: Index as b -> (Edit' :&: SOP.I) b -> Maybe b
    go i (e :&: SOP.I x) = patch' e x \\ every @_ @Diff i


-- -- -- --

data SumDiff :: (k -> Type) -> (k -> Type) -> [k] -> Type where
    SDSame :: (Index as :&: Index as :&: g) a -> SumDiff f g as
    SDDiff :: (Index as :&: f) a -> (Index as :&: f) b -> SumDiff f g as

sumIx :: Sum f as -> Some (Index as :&: f)
sumIx = \case
  InL x  -> Some (IZ :&: x)
  InR xs -> case sumIx xs of
    Some (i :&: x) -> Some (IS i :&: x)

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

data ConstructorEdit as = CECC (Prod                         Edit'  as)
                        | CECR (Prod (C String           :&: Edit') as)
                        | CERC (Prod (C String           :&: Edit') as)
                        | CERR (Prod (C (String, String) :&: Edit') as)

diffSOPInfo
    :: forall ass. ()
    => SOP.DatatypeInfo ass
    -> SumDiff Tuple (Prod Edit') ass
    -> SumDiff (C SOP.ConstructorName :&: Tuple)
               (C (SOP.ConstructorName, SOP.ConstructorName) :&: ConstructorEdit)
               ass
diffSOPInfo dti = \case
    SDSame (i :&: j :&: x)       ->
      SDSame ( i
           :&: j
           :&: (C (cLab i, cLab j) :&: (cEdit i j) x)
             )
    SDDiff (i :&: xs) (j :&: ys) ->
      SDDiff (i :&: (C (cLab i) :&: xs))
             (j :&: (C (cLab j) :&: ys))
  where
    cEdit
        :: Index ass as
        -> Index ass as
        -> Prod Edit' as
        -> ConstructorEdit as
    cEdit i j = case (TCP.index i cInfo, TCP.index j cInfo) of
        (SOP.Record _ f1, SOP.Record _ f2) ->
            CERR
          . zipProdWith gorr (zipProd (sopProd f1) (sopProd f2))
        (_, SOP.Record _ f2) -> CECR
                              . zipProdWith ((:&:) . C . SOP.fieldName) (sopProd f2)
        (SOP.Record _ f1, _) -> CERC
                              . zipProdWith ((:&:) . C . SOP.fieldName) (sopProd f1)
        (_, _)               -> CECC
      where
        gorr
            :: (SOP.FieldInfo :&: SOP.FieldInfo) a
            -> Edit' a
            -> (C (String, String) :&: Edit') a
        gorr (f1 :&: f2) e = C (SOP.fieldName f1, SOP.fieldName f2) :&: e
    cLab :: Index ass as -> SOP.ConstructorName
    cLab i = SOP.constructorName
           . TCP.index i
           $ cInfo
    cInfo :: Prod SOP.ConstructorInfo ass
    cInfo = sopProd . SOP.constructorInfo $ dti

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
  where
    go  :: Every Diff as => Index as a -> (Edit' :&: I) a -> Maybe a
    go k (e :&: I x) = patch' e x \\ every @_ @Diff k









zipProd
    :: Prod f as
    -> Prod g as
    -> Prod (f :&: g) as
zipProd = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y :< ys -> (x :&: y) :< zipProd xs ys

izipProdWith
    :: forall f g h as. ()
    => (forall a. Index as a -> f a -> g a -> h a)
    -> Prod f as
    -> Prod g as
    -> Prod h as
izipProdWith f = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y :< ys -> f IZ x y :< izipProdWith (f . IS) xs ys

zipProdWith
    :: forall f g h as. ()
    => (forall a. f a -> g a -> h a)
    -> Prod f as
    -> Prod g as
    -> Prod h as
zipProdWith f = go
  where
    go  :: Prod f bs
        -> Prod g bs
        -> Prod h bs
    go = \case
      Ø -> \case
        Ø -> Ø
      x :< xs -> \case
        y :< ys -> f x y :< go xs ys

sopSum :: SOP.NS f as -> Sum f as
sopSum = \case
    SOP.Z x  -> InL x
    SOP.S xs -> InR (sopSum xs)

sopProd :: SOP.NP f as -> Prod f as
sopProd = \case
    SOP.Nil     -> Ø
    x SOP.:* xs -> x :< sopProd xs

sopSOP :: SOP.SOP f ass -> Sum (Prod f) ass
sopSOP = map1 sopProd . sopSum . SOP.unSOP

sumSOP :: Sum f as -> SOP.NS f as
sumSOP = \case
    InL x  -> SOP.Z x
    InR xs -> SOP.S (sumSOP xs)

prodSOP :: Prod f as -> SOP.NP f as
prodSOP = \case
    Ø       -> SOP.Nil
    x :< xs -> x SOP.:* prodSOP xs

sopSop :: Sum (Prod f) ass -> SOP.SOP f ass
sopSop = SOP.SOP . sumSOP . map1 prodSOP

