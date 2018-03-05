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
  , Edit'(..), diff', patch'
  ) where

-- import           Data.Bifunctor
-- import           Type.Family.List
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

patch' :: Diff a => Edit' a -> a -> Maybe a
patch' (Edit' x) = patch x

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

