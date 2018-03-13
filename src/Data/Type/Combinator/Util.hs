{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Combinator.Util (
    zipProd
  , zipProdWith
  , izipProdWith
  , izipProdWithA
  , izipProdWithA_
  , unzipProd
  , sopProd
  , sopSOP
  , sopSop
  , prodSOP
  , sumIx
  , fromSum
  , ifromSum
  , ixNum
  , sListLength
  ) where

import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Class.Higher
import qualified Generics.SOP          as SOP

unzipProd
    :: Prod (f :&: g) as
    -> (Prod f :&: Prod g) as
unzipProd = \case
    Ø                 -> (Ø :&: Ø)
    (x :&: y) :< xsys -> ((x :<) .&. (y :<)) $ unzipProd xsys

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

izipProdWithA
    :: forall f g h t as. Applicative t
    => (forall a. Index as a -> f a -> g a -> t (h a))
    -> Prod f as
    -> Prod g as
    -> t (Prod h as)
izipProdWithA f = \case
    Ø -> \case
      Ø -> pure Ø
    x :< xs -> \case
      y :< ys -> (:<) <$> f IZ x y <*> izipProdWithA (f . IS) xs ys

izipProdWithA_
    :: forall f g t as. Applicative t
    => (forall a. Index as a -> f a -> g a -> t ())
    -> Prod f as
    -> Prod g as
    -> t ()
izipProdWithA_ f = \case
    Ø -> \case
      Ø -> pure ()
    x :< xs -> \case
      y :< ys -> f IZ x y *> izipProdWithA_ (f . IS) xs ys


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

sumIx :: Sum f as -> Some (Index as :&: f)
sumIx = \case
  InL x  -> Some (IZ :&: x)
  InR xs -> case sumIx xs of
    Some (i :&: x) -> Some (IS i :&: x)

fromSum
    :: forall f as r. ()
    => (forall a. f a -> r)
    -> Sum f as
    -> r
fromSum f = go
  where
    go :: Sum f bs -> r
    go = \case
      InL x  -> f x
      InR xs -> go xs

ifromSum
    :: forall f as r. ()
    => (forall a. Index as a -> f a -> r)
    -> Sum f as
    -> r
ifromSum f = \case
    InL x  -> f IZ x
    InR xs -> ifromSum (f . IS) xs

ixNum
    :: Index as a
    -> Int
ixNum = go 0
  where
    go :: Int -> Index bs b -> Int
    go !x = \case
      IZ   -> x
      IS i -> go (x + 1) i

sListLength :: SOP.SList as -> Length as
sListLength = \case
    SOP.SNil  -> LZ
    SOP.SCons -> LS $ sListLength SOP.sList
