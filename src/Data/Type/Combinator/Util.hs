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
  , sopProd
  , sopSOP
  , sopSop
  , prodSOP
  , sumIx
  ) where

import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Class.Higher
import qualified Generics.SOP              as SOP


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

sumIx :: Sum f as -> Some (Index as :&: f)
sumIx = \case
  InL x  -> Some (IZ :&: x)
  InR xs -> case sumIx xs of
    Some (i :&: x) -> Some (IS i :&: x)

