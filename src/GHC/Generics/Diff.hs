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
  ) where

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
import           Type.Family.List
import           Type.Reflection
import qualified Generics.SOP           as SOP

-- import           Generics.SOP
-- import           Generics.SOP.Constraint
-- import qualified GHC.Generics            as G

class Eq a => Diff a where
    data Edit a
    diff :: a -> a -> Edit a

instance (Diff a, Diff b) => Diff (a, b) where
    data Edit (a, b) = ETup (Edit a) (Edit b)

    diff (x1, y1) (x2, y2) = ETup (diff x1 x2) (diff y1 y2)

instance (Diff a, Diff b) => Diff (Either a b) where
    data Edit (Either a b) = L2L (Edit a)
                           | L2R a b
                           | R2L b a
                           | R2R (Edit b)
    diff (Left  x) (Left  y) = L2L (diff x y)
    diff (Left  x) (Right y) = L2R x y
    diff (Right x) (Left  y) = R2L x y
    diff (Right x) (Right y) = R2R (diff x y)

-- instance (ListC (Eq <$> (f <$> as)), ListC (Diff <$> (f <$> as))) => Diff (Prod f as) where
--     data Edit (Prod f as) = EProd (Prod (Edit :.: f) as)
--     diff xs = EProd . diffProd xs

-- zipProd
--     :: Prod f as
--     -> Prod g as
--     -> Prod (f :&: g) as
-- zipProd = \case
--     Ø -> \case
--       Ø -> Ø
--     x :< xs -> \case
--       y :< ys -> (x :&: y) :< zipProd xs ys

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


-- diffProd
--     :: forall f as. (ListC (Diff <$> (f <$> as)))
--     => Prod f as
--     -> Prod f as
--     -> Prod (Edit :.: f) as
-- diffProd = \case
--     Ø -> \case
--       Ø -> Ø
--     x :< xs -> \case
--       y :< ys -> Comp (diff x y) :< diffProd xs ys

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

diffSum
    :: forall as. Every Diff as
    => Sum I as
    -> Sum I as
    -> SumDiff I Edit as
diffSum = sumDiff $ \(i :&: I x :&: I y) -> diff x y \\ every @_ @Diff i

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

-- | Version of diffSum' that considers compatible constructor changes as swaps
diffSum'
    :: forall as. (Every Diff as, Every Typeable as)
    => Sum I as
    -> Sum I as
    -> SumDiff I Edit as
diffSum' = sumDiff' $ \((i :&: I x) :&: (_ :&: I y)) -> diff x y
    \\ every @_ @Diff i

diffSOP
    :: forall ass. Every (Every Diff) ass
    => Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod Edit) ass
diffSOP = sumDiff combine
  where
    combine
        :: forall as. ()
        => (Index ass :&: Tuple :&: Tuple) as
        -> Prod Edit as
    combine (i :&: xs :&: ys) = every @_ @(Every Diff) i //
        izipProdWith go xs ys
      where
        go :: Every Diff as => Index as a -> I a -> I a -> Edit a
        go j (I x) (I y) = diff x y \\ every @_ @Diff j

diffSOP'
    :: forall ass. (Every (Every Diff) ass, Every Typeable ass)
    => Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod Edit) ass
diffSOP' = sumDiff' combine
  where
    combine
        :: forall as. ()
        => ((Index ass :&: Tuple) :&: (Index ass :&: Tuple)) as
        -> Prod Edit as
    combine ((i :&: xs) :&: (_ :&: ys)) = every @_ @(Every Diff) i //
        izipProdWith go xs ys
      where
        go :: Every Diff as => Index as a -> I a -> I a -> Edit a
        go j (I x) (I y) = diff x y \\ every @_ @Diff j

sopSum :: SOP.NS f as -> Sum f as
sopSum = \case
    SOP.Z x  -> InL x
    SOP.S xs -> InR (sopSum xs)

sopProd :: SOP.NP f as -> Prod f as
sopProd = \case
    SOP.Nil     -> Ø
    x SOP.:* xs -> x :< sopProd xs

-- listC
--     :: forall f as a. ListC (f <$> as)
--     => Index as a
--     -> Wit (f a)
-- listC = \case
--     IZ    -> Wit
--     IS ix -> Wit \\ listC @f ix

-- listC2
--     :: forall f g as a. ListC (f <$> (g <$> as))
--     => Index as a
--     -> Wit (f (g a))
-- listC2 = \case
--     IZ    -> Wit
--     IS ix -> Wit \\ listC2 @f @g ix
