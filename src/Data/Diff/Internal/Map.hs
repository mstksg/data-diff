{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

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
import qualified Data.HashMap.Strict   as HM
import qualified Data.IntMap           as IM
import qualified Data.Map              as M

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

instance (Diff a, Ord k) => Patch (MapDiff (M.Map k) a) where
    patchLevel (partitionEithers . map splitVD . toList . getMD -> (lr, b))
        | null lr   = bLevel
        | null b    = NoDiff
        | otherwise = TotalDiff <> bLevel
     where
       bLevel  = catLevels . map patchLevel $ b
    mergePatch xs ys = fmap MD . sequence
                     $ M.unionWith (\x y -> join (mergeVD <$> x <*> y))
                                   (pure <$> getMD xs)
                                   (pure <$> getMD ys)

instance Diff a => Patch (MapDiff IM.IntMap a) where
    patchLevel (partitionEithers . map splitVD . toList . getMD -> (lr, b))
        | null lr   = bLevel
        | null b    = NoDiff
        | otherwise = TotalDiff <> bLevel
     where
       bLevel  = catLevels . map patchLevel $ b
    mergePatch xs ys = fmap MD . sequence
                     $ IM.unionWith (\x y -> join (mergeVD <$> x <*> y))
                                    (pure <$> getMD xs)
                                    (pure <$> getMD ys)

instance (Hashable k, Eq k, Diff a) => Patch (MapDiff (HM.HashMap k) a) where
    patchLevel (partitionEithers . map splitVD . toList . getMD -> (lr, b))
        | null lr   = bLevel
        | null b    = NoDiff
        | otherwise = TotalDiff <> bLevel
     where
       bLevel  = catLevels . map patchLevel $ b
    mergePatch xs ys = fmap MD . sequence
                     $ HM.unionWith (\x y -> join (mergeVD <$> x <*> y))
                                    (pure <$> getMD xs)
                                    (pure <$> getMD ys)
