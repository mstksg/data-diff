{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Diff.Internal.Map (
    -- MapSource(..)
  -- , MapDiff(..)
  ) where

import           Control.Monad
import           Data.Diff.Internal
import           Data.Either
import           Data.Foldable
import           Data.Hashable
import           Data.Semigroup hiding (diff)
import           GHC.Generics          (Generic)
import qualified Data.HashMap.Lazy     as HM
import qualified Data.IntMap           as IM
import qualified Data.Map              as M
import qualified Data.Set              as S

data ValDiff a = VDDel
               | VDIns a
               | VDMod (Edit a)
  deriving (Generic)

deriving instance (Show a, Show (Edit a)) => Show (ValDiff a)

mergeVD :: Diff a => ValDiff a -> ValDiff a -> MergeResult (ValDiff a)
mergeVD   VDDel     VDDel     = NoConflict VDDel
mergeVD   VDDel     (VDIns _) = Incompatible
mergeVD   VDDel     (VDMod _) = Conflict VDDel
mergeVD   (VDIns _) VDDel     = Incompatible
mergeVD l@(VDIns x) (VDIns y)
    | x == y    = NoConflict l
    | otherwise = Conflict l
mergeVD   (VDIns _) (VDMod _) = Incompatible
mergeVD l@(VDMod _) VDDel     = Conflict l
mergeVD   (VDMod _) (VDIns _) = Incompatible
mergeVD   (VDMod e) (VDMod f) = VDMod <$> mergePatch e f

newtype MapDiff m a = MD { getMD :: m (ValDiff a) }
  deriving (Generic)

deriving instance (Show (m (ValDiff a))) => Show (MapDiff m a)
deriving instance (Eq (m (ValDiff a))) => Eq (MapDiff m a)
deriving instance (Ord (m (ValDiff a))) => Ord (MapDiff m a)
deriving instance (Read (m (ValDiff a))) => Read (MapDiff m a)

splitVD :: ValDiff a -> Either (Maybe a) (Edit a)
splitVD VDDel     = Left Nothing
splitVD (VDIns x) = Left (Just x)
splitVD (VDMod e) = Right e

fpl :: (Diff a, Foldable m) => MapDiff m a -> DiffLevel
fpl (partitionEithers . map splitVD . toList . getMD -> (lr, b))
     | null lr   = bLevel
     | null b    = NoDiff
     | otherwise = TotalDiff <> bLevel
  where
    bLevel  = catLevels . map patchLevel $ b

fmp :: (Traversable m, Diff a)
    => (forall b. (b -> b -> b) -> m b -> m b -> m b)
    -> MapDiff m a
    -> MapDiff m a
    -> MergeResult (MapDiff m a)
fmp f (MD xs) (MD ys) = fmap MD . sequence
                      $ f (\x y -> join (mergeVD <$> x <*> y))
                          (pure <$> xs)
                          (pure <$> ys)

instance (Diff a, Ord k) => Patch (MapDiff (M.Map k) a) where
    patchLevel = fpl
    mergePatch = fmp M.unionWith

instance Diff a => Patch (MapDiff IM.IntMap a) where
    patchLevel = fpl
    mergePatch = fmp IM.unionWith

instance (Hashable k, Eq k, Diff a) => Patch (MapDiff (HM.HashMap k) a) where
    patchLevel = fpl
    mergePatch = fmp HM.unionWith

md  :: Functor m
    => (forall b. [m b] -> m b)
    -> (forall b. m b -> m b -> m b)
    -> (m a -> m a -> m (Edit a))
    -> m a
    -> m a
    -> MapDiff m a
md unions difference intersect m1 m2 = MD $ unions [ VDDel <$ l
                                                   , VDIns <$> r
                                                   , VDMod <$> b
                                                   ]
  where
    l = difference m1 m2
    r = difference m2 m1
    b = intersect m1 m2

mp  :: forall m k a. ()
    => (forall b c. (b -> k -> c -> b) -> b -> m c -> b)
    -> (ValDiff a -> k -> m a -> Maybe (m a))
    -> MapDiff m a
    -> m a
    -> Maybe (m a)
mp folder alter (MD es) m0 = folder go (Just m0) es
  where
    go :: Maybe (m a) -> k -> ValDiff a -> Maybe (m a)
    go m1 k v = alter v k =<< m1

alterFunc :: Diff a => ValDiff a -> Maybe a -> Maybe (Maybe a)
alterFunc = \case
  VDDel -> \case
    Nothing -> Nothing
    Just _  -> Just Nothing
  VDIns x -> \case
    Nothing -> Just (Just x)
    Just _  -> Nothing
  VDMod e -> \case
    Nothing -> Nothing
    Just x  -> Just <$> patch e x

instance (Ord k, Diff a) => Diff (M.Map k a) where
    type Edit (M.Map k a) = MapDiff (M.Map k) a
    diff = md M.unions M.difference (M.intersectionWith diff)
    patch = mp M.foldlWithKey' (M.alterF . alterFunc)

instance Diff a => Diff (IM.IntMap a) where
    type Edit (IM.IntMap a) = MapDiff IM.IntMap a
    diff = md IM.unions IM.difference (IM.intersectionWith diff)
    patch = mp IM.foldlWithKey' (IM.alterF . alterFunc)

hmAlterF
    :: (Hashable k, Eq k, Functor f)
    => (Maybe a -> f (Maybe a))
    -> k
    -> HM.HashMap k a
    -> f (HM.HashMap k a)
hmAlterF f k m = (\case Nothing -> HM.delete k m
                        Just x  -> HM.insert k x m
                 )
             <$> f (HM.lookup k m)

instance (Hashable k, Eq k, Diff a) => Diff (HM.HashMap k a) where
    type Edit (HM.HashMap k a) = MapDiff (HM.HashMap k) a
    diff = md HM.unions HM.difference (HM.intersectionWith diff)
    patch = mp HM.foldlWithKey' (hmAlterF . alterFunc)

