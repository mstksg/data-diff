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
  , CtrDiff(..)
  , diffSOP
  , diffSOP'
  , patchSOP
  , undiffSOP
  ) where

-- import           Data.Bifunctor
-- import           Data.Function
import           Control.Monad
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
    SD :: (Index as :&: CtrDiff f g as) a -> SumDiff f g as

data CtrDiff :: (k -> Type) -> (k -> Type) -> [k] -> k -> Type where
    CDEdit :: g a -> CtrDiff f g as a
    CDName :: (Index as :&: g) a -> CtrDiff f g as a
    CDDiff :: f a -> (Index as :&: f) b -> CtrDiff f g as a

-- | Version of 'sumDiff'' that treats constructor changes as total edits
-- even if the contents have the same type
sumDiff'
    :: forall f g as. ()
    => (forall a. (Index as :&: f :&: f) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff' f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
    case testEquality i j of
      Just Refl -> SD ( i :&: CDEdit (f (i :&: x :&: y)) )
      Nothing   -> SD ( i :&: CDDiff x (j :&: y)  )

-- | Version of 'sumDiff' that treats constructor changes as partial edits
-- if the contents have the same type
sumDiff
    :: forall f g as. Every Typeable as
    => (forall a. Typeable a => ((Index as :&: f) :&: (Index as :&: f)) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
        every @_ @Typeable i //
        every @_ @Typeable j //
    case testEquality (tr i) (tr j) of
      Just Refl
        | i == j    -> SD ( i
                        :&: CDEdit (f ((i :&: x) :&: (j :&: y)))
                          )
        | otherwise -> SD ( i
                        :&: CDName (j :&: f ((i :&: x) :&: (j :&: y)))
                          )
      Nothing   -> SD ( i :&: CDDiff x (j :&: y) )
  where
    tr :: Typeable a => p a -> TypeRep a
    tr _ = typeRep

diffSOP'
    :: forall f ass. ()
    => (forall as a. Index ass as -> Index as a -> a -> a -> f a)
    -> Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod f) ass
diffSOP' f = sumDiff' combine
  where
    combine
        :: forall as. ()
        => (Index ass :&: Tuple :&: Tuple) as
        -> Prod f as
    combine (i :&: xs :&: ys) = izipProdWith go xs ys
      where
        go :: Index as a -> I a -> I a -> f a
        go j (I x) (I y) = f i j x y

diffSOP
    :: forall f ass. (Every Typeable ass)
    => (forall as a. Index ass as -> Index as a -> a -> a -> f a)   -- ^ diff
    -> Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod f) ass
diffSOP f = sumDiff combine
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
    => (forall as a. Index ass as -> Index as a -> f a -> a -> Maybe a)     -- ^ patch
    -> (forall as a. Index ass as -> Index as a -> a -> a -> Bool)          -- ^ eq
    -> SumDiff Tuple (Prod f) ass
    -> Sum Tuple ass
    -> Maybe (Sum Tuple ass)
patchSOP f g = \case
    SD (i :&: CDEdit es) -> \xss -> do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go i k) (zipProd es xs)
      return (injectSum i ys)
    SD (i :&: CDName (j :&: es)) -> \xss -> do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go i k) (zipProd es xs)
      return (injectSum j ys)
    SD (i :&: CDDiff xs (j :&: ys)) -> \xss -> do
      xs' <- TCS.index i xss            -- TODO: should this be verified?
      izipProdWithA_ (\k (I x') (I x) -> guard $ g i k x' x) xs' xs
      return (injectSum j ys)
  where
    go  :: Index ass as -> Index as a -> (f :&: I) a -> Maybe a
    go i k (e :&: I x) = f i k e x

undiffSOP
    :: (forall as a. Index ass as -> Index as a -> f a -> (a, a))
    -> SumDiff Tuple (Prod f) ass
    -> (Sum Tuple :&: Sum Tuple) ass
undiffSOP f (SD (i :&: cd)) = case cd of
    CDEdit es -> (injectSum i .&. injectSum i)
               . unzipProd
               . imap1 (\j e -> let (x, y) = f i j e
                                in  I x :&: I y
                       )
               $ es
    CDName (j :&: es) -> (injectSum i .&. injectSum j)
                       . unzipProd
                       . imap1 (\k e -> let (x, y) = f i k e
                                        in  I x :&: I y
                               )
                       $ es
    CDDiff xs (j :&: ys) -> injectSum i xs :&: injectSum j ys
