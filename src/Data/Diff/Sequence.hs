
module Data.Diff.Sequence (
    listDiff
  , patchList
  , SeqDiff(..)
  , seqDiff
  , patchSeq
  ) where

import           Control.Monad
import           Data.Diff.Internal
import           Data.Function
import qualified Data.Algorithm.Diff as D

newtype SeqDiff a = SD { getSD :: [D.Diff a] }

listDiff
    :: Diff a
    => [a]
    -> [a]
    -> SeqDiff a
listDiff xs = SD . D.getDiffBy noDiff xs

seqDiff
    :: Diff a
    => (t -> [a])
    -> t
    -> t
    -> SeqDiff a
seqDiff f = listDiff `on` f

patchSeq
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> SeqDiff a
    -> t
    -> Maybe t
patchSeq f g d = fmap g . patchList d . f

patchList
    :: Eq a
    => SeqDiff a
    -> [a]
    -> Maybe [a]
patchList (SD es0) = go es0
  where
    go (D.First x  : es) xs = (x :) <$> contract x es xs
    go (D.Second x : es) xs = (x :) <$> go es xs
    go (D.Both x y : es) xs = (y :) <$> contract x es xs
    go []                [] = Just []
    go []                _  = Nothing
    contract x es xs = do
      x' : xs' <- pure xs
      guard (x == x')
      go es xs'
