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


module Data.Diff.Internal.Generics (
    SumDiff(..)
  , diffSOP
  , diffSOP'
  , patchSOP
  ) where

import           Data.Kind
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

data SumDiff :: (k -> Type) -> (k -> Type) -> [k] -> Type where
    SDEdit :: (Index as :&: g) a -> SumDiff f g as
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
      Just Refl -> SDEdit (i :&: f (i :&: x :&: y))
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
      Just Refl
        | i == j    -> SDEdit (i :&: f ((i :&: x) :&: (j :&: y)))
        | otherwise -> SDSame (i :&: j :&: f ((i :&: x) :&: (j :&: y)))
      Nothing   -> SDDiff i (j :&: y)
  where
    tr :: Typeable a => p a -> TypeRep a
    tr _ = typeRep

diffSOP
    :: forall f ass. ()
    => (forall as a. Index ass as -> Index as a -> a -> a -> f a)
    -> Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod f) ass
diffSOP f = sumDiff combine
  where
    combine
        :: forall as. ()
        => (Index ass :&: Tuple :&: Tuple) as
        -> Prod f as
    combine (i :&: xs :&: ys) = izipProdWith go xs ys
      where
        go :: Index as a -> I a -> I a -> f a
        go j (I x) (I y) = f i j x y

diffSOP'
    :: forall f ass. (Every Typeable ass)
    => (forall as a. Index ass as -> Index as a -> a -> a -> f a)
    -> Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod f) ass
diffSOP' f = sumDiff' combine
  where
    combine
        :: forall as. ()
        => ((Index ass :&: Tuple) :&: (Index ass :&: Tuple)) as
        -> Prod f as
    combine ((i :&: xs) :&: (_ :&: ys)) = izipProdWith go xs ys
      where
        go :: Index as a -> I a -> I a -> f a
        go j (I x) (I y) = f i j x y

patchSOP
    :: forall f ass. ()
    => (forall as a. Index ass as -> Index as a -> f a -> a -> Maybe a)
    -> SumDiff Tuple (Prod f) ass
    -> Sum Tuple ass
    -> Maybe (Sum Tuple ass)
patchSOP f = \case
    SDEdit (i :&: es) -> \xss -> do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go i k) (zipProd es xs)
      return (injectSum i ys)
    SDSame (i :&: j :&: es) -> \xss -> do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go i k) (zipProd es xs)
      return (injectSum j ys)
    SDDiff i (j :&: ys) -> \xss -> do
      _  <- TCS.index i xss
      return (injectSum j ys)
  where
    go  :: Index ass as -> Index as a -> (f :&: I) a -> Maybe a
    go i k (e :&: I x) = f i k e x
