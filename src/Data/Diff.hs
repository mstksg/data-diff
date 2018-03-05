{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Diff (
    Diff(..)
  , Edit'(..), diff', patch'
  ) where

class Eq a => Diff a where
    type Edit a
    diff      :: a -> a -> Edit a
    patch     :: Edit a -> a -> Maybe a

newtype Edit' a = Edit' { getEdit' :: Edit a }

diff' :: Diff a => a -> a -> Edit' a
diff' x y = Edit' (diff x y)

patch' :: Diff a => Edit' a -> a -> Maybe a
patch' (Edit' x) = patch x

instance (Diff a, Diff b) => Diff (a, b) where
    type Edit (a, b) = (Edit a, Edit b)
    diff (x1, y1) (x2, y2) = (diff x1 x2, diff y1 y2)
    patch (ex, ey) (x, y) = (,) <$> patch   ex x <*> patch   ey y

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

