{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Data.Diff.Internal.Sequence (
  -- * Diff
    SeqPatchAt(..)
  , SeqPatch
  , listDiff
  , listPatch
  , listUndiff
  , seqDiff
  , seqPatch
  , seqUndiff
  -- * Eq
  , EqSeqPatch(..)
  , eqListDiff
  , eqListPatch
  , eqListUndiff
  , eqSeqDiff
  , eqSeqPatch
  , eqSeqUndiff
  -- * Line-by-line
  , LinesPatch(..)
  , Lines(..)
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Internal
import           Data.Function
import           Data.Hashable
import           Data.Maybe
import           Data.Proxy
import           Data.Semigroup hiding        (diff)
import           GHC.Generics                 (Generic)
import           GHC.TypeNats
import qualified Data.Algorithm.Diff          as D
import qualified Data.Algorithm.Diff3         as D
import qualified Data.HashSet                 as HS
import qualified Data.IntSet                  as IS
import qualified Data.Semigroup               as S
import qualified Data.Set                     as S
import qualified Data.String.Conversions      as SC
import qualified Data.Text                    as T
import qualified Data.Text.Lazy               as TL
import qualified Data.Vector                  as V
import qualified Data.Vector.Primitive        as VP
import qualified Data.Vector.Storable         as VS
import qualified Data.Vector.Unboxed          as VU
import qualified GHC.Exts                     as E
import qualified Text.PrettyPrint.ANSI.Leijen as PP

newtype SeqPatchAt (p :: Nat) a = SPA { getSPA :: [D.Diff a] }
  deriving (Show, Eq, Generic)

instance (KnownNat p, Diff a) => Patch (SeqPatchAt p a) where
    patchLevel = catLevels . map dLevel . getSPA
      where
        dLevel :: D.Diff a -> DiffLevel
        dLevel (D.First _ ) = TotalDiff 1
        dLevel (D.Second _) = TotalDiff 1
        dLevel (D.Both x y) = compareDiff x y
    mergePatch es1 es2
        | xs1 == xs2 = listDiff xs1
                     . concat
                   <$> traverse dehunk (D.diff3By (threshFunc @p) ys xs1 zs)
        | otherwise  = Incompatible
      where
        (xs1, ys) = listUndiff es1
        (xs2, zs) = listUndiff es2

instance (KnownNat p, Diff a, Show a, ShowPatch (Edit a)) => ShowPatch (SeqPatchAt p a) where
    showPatch es = PP.vcat . mapMaybe go $ getSPA es
      where
        go :: D.Diff a -> Maybe PP.Doc
        go (D.First  x) = Just $ PP.red    (PP.char '-') <> PP.text (show x)
        go (D.Second x) = Just $ PP.green  (PP.char '+') <> PP.text (show x)
        go (D.Both x y)
            | x == y    = Nothing
            | otherwise = Just $ PP.yellow (PP.char '~') <> showPatch (diff x y)

type SeqPatch = SeqPatchAt 50

newtype EqSeqPatch a = ESP { getESP :: SeqPatchAt 0 (EqDiff a) }
  deriving (Show, Eq, Patch, Generic)

newtype LinesPatch t = LP { getLP :: EqSeqPatch T.Text }
  deriving (Show, Eq, Patch, Generic)

dehunk
    :: forall a. Diff a
    => D.Hunk a
    -> MergeResult [a]
dehunk = \case
    D.LeftChange  xs      -> NoConflict xs
    D.RightChange ys      -> NoConflict ys
    D.Unchanged   xyzs    -> traverse go xyzs
    D.Conflict    xs _ ys
      | xs == ys  -> NoConflict xs
      | otherwise -> Conflict xs
  where
    go :: (a, a, a) -> MergeResult a
    go (x,o,y) = do
        p3 <- mergePatch p1 p2
        maybe Incompatible NoConflict $ patch p3 o
      where
        p1 = diff o x
        p2 = diff o y

threshFunc :: forall p a. (KnownNat p, Diff a) => a -> a -> Bool
threshFunc x y = percentDiff x y < p
  where
    p = fromIntegral (natVal (Proxy @p)) / 100

unsafeListDiffBy
    :: (a -> a -> Bool)
    -> [a]
    -> [a]
    -> SeqPatchAt p a
unsafeListDiffBy f xs = SPA . D.getDiffBy f xs

listDiff
    :: forall p a. (KnownNat p, Diff a)
    => [a]
    -> [a]
    -> SeqPatchAt p a
listDiff = unsafeListDiffBy $ threshFunc @p

eqListDiff
    :: Eq a
    => [a]
    -> [a]
    -> EqSeqPatch a
eqListDiff x = ESP . listDiff (EqDiff <$> x) . fmap EqDiff

seqDiff
    :: (KnownNat p, Diff a)
    => (t -> [a])
    -> t
    -> t
    -> SeqPatchAt p a
seqDiff f = listDiff `on` f

eqSeqDiff
    :: Eq a
    => (t -> [a])
    -> t
    -> t
    -> EqSeqPatch a
eqSeqDiff f = eqListDiff `on` f

seqPatch
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> SeqPatchAt p a
    -> t
    -> Maybe t
seqPatch f g d = fmap g . listPatch d . f

seqUndiff
    :: ([a] -> t)
    -> SeqPatchAt p a
    -> (t, t)
seqUndiff f = bimap f f . listUndiff

eqSeqPatch
    :: Eq a
    => (t -> [a])
    -> ([a] -> t)
    -> EqSeqPatch a
    -> t
    -> Maybe t
eqSeqPatch f g d = fmap g . eqListPatch d . f

eqSeqUndiff
    :: Eq a
    => ([a] -> t)
    -> EqSeqPatch a
    -> (t, t)
eqSeqUndiff f = bimap f f . eqListUndiff

listPatch
    :: Eq a
    => SeqPatchAt p a
    -> [a]
    -> Maybe [a]
listPatch = go . getSPA
  where
    go (D.First x  : es) xs = contract x es xs
    go (D.Second x : es) xs = (x :) <$> go es xs
    go (D.Both x y : es) xs = (y :) <$> contract x es xs
    go []                [] = Just []
    go []                _  = Nothing
    contract x es xs = do
      x' : xs' <- pure xs
      guard (x == x')
      go es xs'

eqListPatch
    :: Eq a
    => EqSeqPatch a
    -> [a]
    -> Maybe [a]
eqListPatch p = (fmap . map) getEqDiff . listPatch (getESP p) . map EqDiff

eqListUndiff
    :: EqSeqPatch a
    -> ([a], [a])
eqListUndiff = bimap (map getEqDiff) (map getEqDiff) . listUndiff . getESP

listUndiff
    :: SeqPatchAt p a
    -> ([a], [a])
listUndiff = recover . getSPA
  where
    recover :: forall b. [D.Diff b] -> ([b], [b])
    recover = bimap (`appEndo` []) (`appEndo` []) . foldMap go
      where
        go :: D.Diff b -> (Endo [b], Endo [b])
        go = \case
          D.Both   x y -> (S.diff [x], S.diff [y])
          D.First  x   -> (S.diff [x], mempty    )
          D.Second   y -> (mempty    , S.diff [y])


instance (E.IsList l, e ~ E.Item l, Diff e, KnownNat p) => DefaultDiff (SeqPatchAt p e) l  where
    defaultDiff   = seqDiff E.toList
    defaultPatch  = seqPatch E.toList E.fromList
    defaultUndiff = seqUndiff E.fromList

instance (E.IsList l, e ~ E.Item l, Eq e) => DefaultDiff (EqSeqPatch e) l  where
    defaultDiff   = eqSeqDiff E.toList
    defaultPatch  = eqSeqPatch E.toList E.fromList
    defaultUndiff = eqSeqUndiff E.fromList

instance (SC.ConvertibleStrings t T.Text, SC.ConvertibleStrings T.Text t)
            => DefaultDiff (LinesPatch t) t where
    defaultDiff x = LP . eqSeqDiff (T.splitOn "\n" . SC.convertString) x
    defaultPatch p = fmap SC.convertString
                   . eqSeqPatch (T.splitOn "\n") (T.intercalate "\n") (getLP p)
                   . SC.convertString
    defaultUndiff = bimap SC.convertString SC.convertString
                  . eqSeqUndiff (T.intercalate "\n")
                  . getLP

-- | Items that aren't completely different are considered modifications,
-- not insertions/deletions.  If this is not desired behavior, map with
-- 'EqDiff'.
instance Diff a => Diff [a] where
    type Edit [a] = SeqPatch a

-- | See notes for list instance.
instance Diff a => Diff (V.Vector a) where
    type Edit (V.Vector a) = SeqPatch a

-- | See notes for list instance.
instance (Diff a, VS.Storable a) => Diff (VS.Vector a) where
    type Edit (VS.Vector a) = SeqPatch a

-- | See notes for list instance.
instance (Diff a, VU.Unbox a) => Diff (VU.Vector a) where
    type Edit (VU.Vector a) = SeqPatch a

-- | See notes for list instance.
instance (Diff a, VP.Prim a) => Diff (VP.Vector a) where
    type Edit (VP.Vector a) = SeqPatch a

-- | Line-by-line diff
instance Diff T.Text where
    type Edit T.Text = LinesPatch T.Text

-- | Line-by-line diff
instance Diff TL.Text where
    type Edit TL.Text = LinesPatch TL.Text

-- | Newtype wrapper for line-by-line diffing
newtype Lines t = Lines { getLines :: t }
    deriving (Show, Eq, Read, Generic)

instance SC.ConvertibleStrings s t => SC.ConvertibleStrings s (Lines t) where
    convertString = Lines . SC.convertString

instance SC.ConvertibleStrings t s => SC.ConvertibleStrings (Lines t) s where
    convertString = SC.convertString . getLines

-- | Line-by-line diffing of strings
instance (SC.ConvertibleStrings t T.Text, SC.ConvertibleStrings T.Text t, Eq t)
        => Diff (Lines t) where
    type Edit (Lines t) = LinesPatch (Lines t)

-- | Changes are purely inclusion/exclusion
instance Ord a => Diff (S.Set a) where
    type Edit (S.Set a) = EqSeqPatch a

-- | Changes are purely inclusion/exclusion
instance Diff IS.IntSet where
    type Edit IS.IntSet = EqSeqPatch Int

-- | Changes are purely inclusion/exclusion
instance (Hashable a, Eq a) => Diff (HS.HashSet a) where
    type Edit (HS.HashSet a) = EqSeqPatch a
