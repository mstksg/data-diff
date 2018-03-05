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

module Data.Diff (
    Diff(..)
  , Edit'(..), diff'
  ) where

-- import           Type.Family.List
import           Data.Bifunctor
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
import qualified Generics.SOP           as SOP

class Eq a => Diff a where
    type Edit a
    diff      :: a -> a -> Edit a
    patch     :: Edit a -> a -> Maybe a
    -- flipPatch :: Edit a -> Edit a

newtype Edit' a = Edit' { getEdit' :: Edit a }

diff' :: Diff a => a -> a -> Edit' a
diff' x y = Edit' (diff x y)

instance (Diff a, Diff b) => Diff (a, b) where
    type Edit (a, b) = (Edit a, Edit b)
    diff (x1, y1) (x2, y2) = (diff x1 x2, diff y1 y2)
    patch (ex, ey) (x, y) = (,) <$> patch   ex x <*> patch   ey y
    -- flipPatch = bimap (flipPatch @a) (flipPatch @b)

data EitherEdit a b = L2L (Edit a)
                    | L2R a b
                    | R2L b a
                    | R2R (Edit b)

instance (Diff a, Diff b) => Diff (Either a b) where
    type Edit (Either a b) = EitherEdit a b
    diff (Left  x) (Left  y) = L2L (diff x y)
    diff (Left  x) (Right y) = L2R x y
    diff (Right x) (Left  y) = R2L x y
    diff (Right x) (Right y) = R2R (diff x y)
    patch (L2L e  ) (Left  x) = Left <$> patch e x
    patch (L2R _ y) (Left  _) = Just (Right y)
    patch (R2L _ x) (Right _) = Just (Left  x)
    patch (R2R e  ) (Right y) = Right <$> patch e y
    patch _         _         = Nothing
    -- flipPatch (L2L e  ) = L2L (flipPatch @a e)
    -- flipPatch (L2R x y) = R2L y x
    -- flipPatch (R2L y x) = L2R x y
    -- flipPatch (R2R e  ) = R2R (flipPatch @b e)

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
    -> SumDiff I Edit' as
diffSum = sumDiff $ \(i :&: I x :&: I y) -> diff' x y \\ every @_ @Diff i

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
    -> SumDiff I Edit' as
diffSum' = sumDiff' $ \((i :&: I x) :&: (_ :&: I y)) -> diff' x y
    \\ every @_ @Diff i

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

sopSum :: SOP.NS f as -> Sum f as
sopSum = \case
    SOP.Z x  -> InL x
    SOP.S xs -> InR (sopSum xs)

sopProd :: SOP.NP f as -> Prod f as
sopProd = \case
    SOP.Nil     -> Ø
    x SOP.:* xs -> x :< sopProd xs

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

