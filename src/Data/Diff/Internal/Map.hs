{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
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
    ValDiff(..)
  , MapDiff(..)
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Internal
import           Data.Diff.Pretty
import           Data.Either
import           Data.Foldable
import           Data.Hashable
import           Data.Maybe
import           GHC.Generics                 (Generic)
import qualified Data.HashMap.Lazy            as HM
import qualified Data.IntMap                  as IM
import qualified Data.Map                     as M
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data ValDiff a = VDDel a
               | VDIns a
               | VDMod (Edit a)
  deriving (Generic)

deriving instance (Show a, Show (Edit a)) => Show (ValDiff a)

mergeVD :: Diff a => ValDiff a -> ValDiff a -> MergeResult (ValDiff a)
mergeVD l@(VDDel x) (VDDel y)
    | x == y    = NoConflict l
    | otherwise = Incompatible
mergeVD   (VDDel _) (VDIns _) = Incompatible
mergeVD l@(VDDel _) (VDMod _) = Conflict l
mergeVD   (VDIns _) (VDDel _) = Incompatible
mergeVD l@(VDIns x) (VDIns y)
    | x == y    = NoConflict l
    | otherwise = Conflict l
mergeVD   (VDIns _) (VDMod _) = Incompatible
mergeVD l@(VDMod _) (VDDel _) = Conflict l
mergeVD   (VDMod _) (VDIns _) = Incompatible
mergeVD   (VDMod e) (VDMod f) = VDMod <$> mergePatch e f

newtype MapDiff m a = MD { getMD :: m (ValDiff a) }
  deriving (Generic)

deriving instance (Show (m (ValDiff a))) => Show (MapDiff m a)
deriving instance (Eq (m (ValDiff a))) => Eq (MapDiff m a)
deriving instance (Ord (m (ValDiff a))) => Ord (MapDiff m a)
deriving instance (Read (m (ValDiff a))) => Read (MapDiff m a)

splitVD :: ValDiff a -> Either (Either a a) (Edit a)
splitVD (VDDel x) = Left (Left  x)
splitVD (VDIns x) = Left (Right x)
splitVD (VDMod e) = Right e

undiffVD :: Diff a => ValDiff a -> (Maybe a, Maybe a)
undiffVD (VDDel x) = (Just x , Nothing)
undiffVD (VDIns x) = (Nothing, Just x)
undiffVD (VDMod e) = bimap Just Just $ undiff e

fpl :: (Diff a, Foldable m) => MapDiff m a -> DiffLevel
fpl (partitionEithers . map splitVD . toList . getMD -> (lr, b))
     | null lr   = catLevels bLevels
     | null b    = NoDiff 1
     | otherwise = catLevels $ (TotalDiff 1 <$ toList lr) ++ bLevels
  where
    bLevels = map patchLevel b

fmp :: (Traversable m, Diff a)
    => (forall b. (b -> b -> b) -> m b -> m b -> m b)
    -> MapDiff m a
    -> MapDiff m a
    -> MergeResult (MapDiff m a)
fmp f (MD xs) (MD ys) = fmap MD . sequence
                      $ f (\x y -> join (mergeVD <$> x <*> y))
                          (pure <$> xs)
                          (pure <$> ys)

fsp :: forall m k a. (Show k, Show a, ShowPatch (Edit a))
    => (m (ValDiff a) -> [(k, ValDiff a)])
    -> MapDiff m a
    -> PP.Doc
fsp f = PP.vcat . mapMaybe (uncurry go) . f . getMD
  where
    go :: k -> ValDiff a -> Maybe PP.Doc
    go k = \case
      VDDel _ -> Just . ppDel $ PP.text ("key " ++ show k)
      VDIns x -> Just . ppAdd $ PP.text ("key " ++ show k ++ ", val " ++ show x)
      VDMod e -> case patchLevel e of
        NoDiff _ -> Nothing
        _        -> Just $ ppMod (PP.text ("key " ++ show k ++ ", val"))
                    PP.<+> showPatch e


instance (Diff a, Ord k) => Patch (MapDiff (M.Map k) a) where
    patchLevel = fpl
    mergePatch = fmp M.unionWith

instance Diff a => Patch (MapDiff IM.IntMap a) where
    patchLevel = fpl
    mergePatch = fmp IM.unionWith

instance (Hashable k, Eq k, Diff a) => Patch (MapDiff (HM.HashMap k) a) where
    patchLevel = fpl
    mergePatch = fmp HM.unionWith

instance (Diff a, Ord k, Show k, Show a, ShowPatch (Edit a)) => ShowPatch (MapDiff (M.Map k) a) where
    showPatch = fsp M.toList

instance (Diff a, Show a, ShowPatch (Edit a)) => ShowPatch (MapDiff IM.IntMap a) where
    showPatch = fsp IM.toList

instance (Diff a, Hashable k, Eq k, Show k, Show a, ShowPatch (Edit a)) => ShowPatch (MapDiff (HM.HashMap k) a) where
    showPatch = fsp HM.toList

md  :: Functor m
    => (forall b. [m b] -> m b)
    -> (forall b. m b -> m b -> m b)
    -> (m a -> m a -> m (Edit a))
    -> m a
    -> m a
    -> MapDiff m a
md unions difference intersect m1 m2 = MD $ unions [ VDDel <$> l
                                                   , VDIns <$> r
                                                   , VDMod <$> b
                                                   ]
  where
    l = difference m1 m2
    r = difference m2 m1
    b = m1 `intersect` m2

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
  VDDel _ -> \case
    Nothing -> Nothing
    Just _  -> Just Nothing
  VDIns x -> \case
    Nothing -> Just (Just x)
    Just _  -> Nothing
  VDMod e -> \case
    Nothing -> Nothing
    Just x  -> Just <$> patch e x

mu  :: Diff a
    => (m (ValDiff a) -> [(k, ValDiff a)])
    -> ([(k, a)] -> m a)
    -> MapDiff m a
    -> (m a, m a)
mu f g (MD es) = bimap g g
               . (\xs -> ( mapMaybe (sequence . second fst) xs
                         , mapMaybe (sequence . second snd) xs
                         )
                 )
               . (map . second) undiffVD
               . f
               $ es

instance (Ord k, Diff a) => Diff (M.Map k a) where
    type Edit (M.Map k a) = MapDiff (M.Map k) a
    diff   = md M.unions M.difference (M.intersectionWith diff)
    patch  = mp M.foldlWithKey' (M.alterF . alterFunc)
    undiff = mu M.toList M.fromAscList

instance Diff a => Diff (IM.IntMap a) where
    type Edit (IM.IntMap a) = MapDiff IM.IntMap a
    diff = md IM.unions IM.difference (IM.intersectionWith diff)
    patch = mp IM.foldlWithKey' (IM.alterF . alterFunc)
    undiff = mu IM.toList IM.fromAscList

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
    undiff = mu HM.toList HM.fromList

