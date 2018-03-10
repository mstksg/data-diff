{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Data.Diff.Internal (
    Diff(..)
  , Patch(..), DiffLevel(.., NoDiff, TotalDiff), MergeResult(..)
  , merge, catLevels, normDL, dlPercent, diffPercentage
  , compareDiff
  , Edit'(..), diff', patch'
  , Swap(..), eqDiff, eqPatch
  , EqDiff(..)
  , gpatchLevel
  , gmergePatch
  , GPatch(..)
  , gdiff
  , gdiff'
  , gpatch
  , GPatchProd(..)
  , gdiffProd
  , gpatchProd
  ) where

-- import           Control.Applicative
-- import           Data.Foldable
-- import qualified Data.List.NonEmpty       as NE
-- import qualified GHC.Generics             as G
import           Control.Monad
import           Data.Diff.Internal.Generics
import           Data.Function
import           Data.Semigroup              (Semigroup(..))
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           GHC.Generics                (Generic)
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Reflection
import qualified Generics.SOP                as SOP

data DiffLevel = DL Double Double

instance Semigroup DiffLevel where
    DL x s <> DL y t = DL (x + y) (s + t)

instance Monoid DiffLevel where
    mappend = (<>)
    mempty  = DL 0 0

pattern NoDiff :: Double -> DiffLevel
pattern NoDiff t <- DL ((== 0)->True) t
  where
    NoDiff t = DL 0 t

isTot :: DiffLevel -> Maybe Double
isTot (DL y t)
  | abs (y - t) < 0.0001 = Just t
  | otherwise            = Nothing

pattern TotalDiff :: Double -> DiffLevel
pattern TotalDiff x <- (isTot->Just x)
  where
    TotalDiff x = DL x x

-- what about 0?
normDL :: Double -> DiffLevel -> DiffLevel
normDL s (DL x t) = DL (x / t * s) s

dlPercent :: DiffLevel -> Double
dlPercent (DL x t) = x / t

catLevels
    :: Foldable f
    => f DiffLevel
    -> DiffLevel
catLevels = normMaybe . foldMap (normDL 1)
  where
    normMaybe (DL _ 0) = NoDiff 1
    normMaybe dl       = normDL 1 dl

data MergeResult a = Incompatible
                   | Conflict   a
                   | NoConflict a
  deriving (Functor, Show, Eq, Ord)

instance Applicative MergeResult where
    pure  = return
    (<*>) = ap

instance Monad MergeResult where
    return = NoConflict
    rx >>= f = case rx of
      Incompatible -> Incompatible
      Conflict x   -> case f x of
        Incompatible -> Incompatible
        Conflict y   -> Conflict y
        NoConflict y -> Conflict y
      NoConflict x -> case f x of
        Incompatible -> Incompatible
        Conflict y   -> Conflict y
        NoConflict y -> NoConflict y

class Patch a where
    -- | "Level" of patch
    patchLevel :: a -> DiffLevel

    -- | Left-biased parallel merge of two patches
    --
    -- Returns 'Nothing' if patches come from incompatible sources
    --
    -- Returns 'True' if conflict occurred (and was resolved)
    mergePatch :: a -> a -> MergeResult a

    default patchLevel
        :: (SOP.Generic a, Every (Every Patch) (SOP.Code a))
        => a
        -> DiffLevel
    patchLevel = gpatchLevel

    default mergePatch
        :: (SOP.IsProductType a as, Every Patch as)
        => a
        -> a
        -> MergeResult a
    mergePatch = gmergePatch

class (Eq a, Patch (Edit a)) => Diff a where
    type Edit a
    type instance Edit a = GPatch a
    diff      :: a -> a -> Edit a
    patch     :: Edit a -> a -> Maybe a
    -- undiff    :: Edit a -> (a, a)

    default diff
        :: DefaultDiff (Edit a) a
        => a
        -> a
        -> Edit a
    diff = defaultDiff

    default patch
        :: DefaultDiff (Edit a) a
        => Edit a
        -> a
        -> Maybe a
    patch = defaultPatch

    -- default patch
    --     :: ( Edit a ~ GPatch a
    --        , SOP.Generic a
    --        , Every (Every Diff) (SOP.Code a)
    --        )
    --     => Edit a
    --     -> a
    --     -> Maybe a
    -- patch = gpatch

class DefaultDiff p a where
    defaultDiff :: a -> a -> p
    defaultPatch :: p -> a -> Maybe a

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every Typeable (SOP.Code a))
      => DefaultDiff (GPatch a) a where
    defaultDiff  = gdiff'
    defaultPatch = gpatch

-- | Left-biased merge of two diffable values.
merge :: Diff a => a -> a -> a -> MergeResult a
merge o x y = do
    pz <- mergePatch px py
    maybe Incompatible NoConflict $ patch pz o
  where
    px = diff o x
    py = diff o y

newtype Edit' a = Edit' { getEdit' :: Edit a }
    deriving (Generic)

instance SOP.Generic (Edit' a)
instance Patch (Edit a) => Patch (Edit' a)

diff' :: Diff a => a -> a -> Edit' a
diff' x y = Edit' (diff x y)

patch' :: Diff a => Edit' a -> a -> Maybe a
patch' (Edit' x) = patch x

diffPercentage :: Diff a => a -> a -> Double
diffPercentage x y = dlPercent $ patchLevel (diff x y)

compareDiff :: Diff a => a -> a -> DiffLevel
compareDiff x y = patchLevel (diff x y)

gpatchLevel
    :: forall a ass. (SOP.Generic a, SOP.Code a ~ ass, Every (Every Patch) ass)
    => a -> DiffLevel
gpatchLevel = ifromSum go . map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from
  where
    go :: forall as. Index (SOP.Code a) as -> Tuple as -> DiffLevel
    go i = catLevels . ifoldMap1 pl     \\ every @_ @(Every Patch) i
      where
        pl :: Every Patch as => Index as b -> I b -> [DiffLevel]
        pl j = (:[]) . patchLevel . getI \\ every @_ @Patch j

gmergePatch
    :: forall a as. (SOP.IsProductType a as, Every Patch as)
    => a
    -> a
    -> MergeResult a
gmergePatch x0 = fmap (SOP.to . sopSop . InL)
               . traverse1 (fmap SOP.I)
               . go x0
  where
    go :: a -> a -> Prod MergeResult as
    go = izipProdWith (\i (SOP.I x) (SOP.I y) -> mergePatch x y \\ every @_ @Patch i)
      `on` sopProd
         . SOP.unZ
         . SOP.unSOP
         . SOP.from


-- TODO: case w/o typable
newtype GPatch a = GP { getGP :: SumDiff Tuple (Prod Edit') (SOP.Code a) }

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every (Every (Comp Patch Edit')) (SOP.Code a)) => Patch (GPatch a) where
    patchLevel = gpPatchLevel
    mergePatch = gpMergePatch

gpPatchLevel
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> DiffLevel
gpPatchLevel = \case
    GP (SDEdit (i :&: xs))       -> prodPatchLevel xs
                                      \\ every @_ @(Every Diff) i
    GP (SDSame (i :&: _ :&: xs)) -> catLevels [TotalDiff 1, prodPatchLevel xs]
                                      \\ every @_ @(Every Diff) i
    GP (SDDiff _ _) -> TotalDiff 1

prodPatchLevel :: forall as. Every Diff as => Prod Edit' as -> DiffLevel
prodPatchLevel = catLevels . ifoldMap1 go
  where
    go :: Index as a -> Edit' a -> [DiffLevel]
    go i (Edit' e) = [patchLevel e] \\ every @_ @Diff i

-- TODO: factor out i1
gpMergePatch
    :: (Every (Every (Comp Patch Edit')) (SOP.Code a), Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> GPatch a
    -> MergeResult (GPatch a)
gpMergePatch = \case
    l@(GP (SDEdit (i1 :&: es1))) -> \case
      GP (SDEdit (i2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl -> do
          es <- prodMergePatch es1 es2      \\ every @_ @(Every (Comp Patch Edit')) i1
          pure (GP (SDEdit (i1 :&: es)))
        Nothing -> Incompatible
      GP (SDSame (i2 :&: j2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl -> do
          es <- prodMergePatch es1 es2      \\ every @_ @(Every (Comp Patch Edit')) i1
          pure (GP (SDSame (i2 :&: j2 :&: es)))
        Nothing -> Incompatible
      r@(GP (SDDiff i2 (_ :&: _))) -> case testEquality i1 i2 of
        Just Refl ->
          -- TODO: factor out
          let levels :: [DiffLevel]
              levels = ifoldMap1 (\i e -> [patchLevel e] \\ every @_ @(Comp Patch Edit') i) es1
                          \\ every @_ @(Every (Comp Patch Edit')) i1
          in  case catLevels levels of
                NoDiff _ -> NoConflict r
                _        -> Conflict l
        Nothing   -> Incompatible
    l@(GP (SDSame (i1 :&: j1 :&: es1))) -> \case
      GP (SDEdit (i2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl -> do
          es <- prodMergePatch es1 es2      \\ every @_ @(Every (Comp Patch Edit')) i1
          pure (GP (SDSame (i1 :&: j1 :&: es)))
        Nothing -> Incompatible
      GP (SDSame (i2 :&: j2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl -> do
          es <- prodMergePatch es1 es2      \\ every @_ @(Every (Comp Patch Edit')) i1
          case testEquality j1 j2 of
            Just Refl -> NoConflict . GP $ SDSame (i1 :&: j1 :&: es)
            Nothing   -> Conflict   . GP $ SDSame (i1 :&: j1 :&: es)
        Nothing -> Incompatible
      GP (SDDiff i2 (_ :&: _)) -> case testEquality i1 i2 of
        Just Refl -> Conflict l
        Nothing   -> Incompatible
    l@(GP (SDDiff i1 (j1 :&: es1))) -> \case
      GP (SDEdit (i2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl ->
          let levels :: [DiffLevel]
              levels = ifoldMap1 (\i e -> [patchLevel e] \\ every @_ @(Comp Patch Edit') i) es2
                          \\ every @_ @(Every (Comp Patch Edit')) i2
          in  case catLevels levels of
                NoDiff _ -> NoConflict l
                _        -> Conflict l
        Nothing -> Incompatible
      GP (SDSame (i2 :&: _ :&: _)) -> case testEquality i1 i2 of
        Just Refl -> Conflict l
        Nothing   -> Incompatible
      GP (SDDiff i2 (j2 :&: es2)) -> case testEquality i1 i2 of
        Just Refl -> case testEquality j1 j2 of
          Just Refl -> do
            es <- izipProdWithA (\i (I e1) (I e2) ->
                                    I <$> if e1 == e2 \\ every @_ @Diff i
                                      then NoConflict e1
                                      else Conflict   e1
                                )
                    es1
                    es2     \\ every @_ @(Every Diff) j1
            pure $ GP (SDDiff i1 (j1 :&: es))
          Nothing   -> Conflict l
        Nothing   -> Incompatible

prodMergePatch
    :: forall as. Every (Comp Patch Edit') as
    => Prod Edit' as
    -> Prod Edit' as
    -> MergeResult (Prod Edit' as)
prodMergePatch = izipProdWithA go
  where
    go  :: Index as a
        -> Edit' a
        -> Edit' a
        -> MergeResult (Edit' a)
    go i x y = mergePatch x y \\ every @_ @(Comp Patch Edit') i

gdiff
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => a
    -> a
    -> GPatch a
gdiff x y = GP $ go x y
  where
    go = diffSOP d `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from
      where
        d :: Index (SOP.Code a) as -> Index as b -> b -> b -> Edit' b
        d i j = diff' \\ every @_ @Diff         j
                      \\ every @_ @(Every Diff) i

gdiff'
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every Typeable (SOP.Code a))
    => a
    -> a
    -> GPatch a
gdiff' x y = GP $ go x y
  where
    go = diffSOP' d `on` map1 (map1 (I . SOP.unI)) . sopSOP . SOP.from
      where
        d :: Index (SOP.Code a) as -> Index as b -> b -> b -> Edit' b
        d i j = diff' \\ every @_ @Diff         j
                      \\ every @_ @(Every Diff) i


gpatch
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> a
    -> Maybe a
gpatch e = fmap (SOP.to . sopSop . map1 (map1 (SOP.I . getI)))
         . patchSOP p (getGP e)
         . map1 (map1 (I . SOP.unI))
         . sopSOP
         . SOP.from
  where
    p :: Index (SOP.Code a) as -> Index as b -> Edit' b -> b -> Maybe b
    p i j = patch' \\ every @_ @Diff         j
                   \\ every @_ @(Every Diff) i

data GPatchProd a = forall as. (SOP.Code a ~ '[as])
                 => GPP { getGPP :: Prod Edit' as }

instance (SOP.IsProductType a as, Every Diff as, Every (Comp Patch Edit') as) => Patch (GPatchProd a) where
    patchLevel (GPP es) = prodPatchLevel es
    mergePatch (GPP es1) (GPP es2) = GPP <$> prodMergePatch es1 es2

instance (SOP.IsProductType a as, Every Diff as) => DefaultDiff (GPatchProd a) a where
    defaultDiff  = gdiffProd
    defaultPatch = gpatchProd

gdiffProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => a
    -> a
    -> GPatchProd a
gdiffProd x y = GPP $ go x y
  where
    go :: a -> a -> Prod Edit' as
    go = izipProdWith (\i -> d i `on` SOP.unI) `on`
           sopProd . SOP.unZ . SOP.unSOP . SOP.from
    d :: Index as b -> b -> b -> Edit' b
    d i = diff' \\ every @_ @Diff i

gpatchProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => GPatchProd a
    -> a
    -> Maybe a
gpatchProd (GPP es) =
      fmap (SOP.to . SOP.SOP . SOP.Z . prodSOP)
    . itraverse1 (\i -> fmap SOP.I . go i)
    . zipProd es
    . sopProd
    . SOP.unZ
    . SOP.unSOP
    . SOP.from
  where
    go :: Index as b -> (Edit' :&: SOP.I) b -> Maybe b
    go i (e :&: SOP.I x) = patch' e x \\ every @_ @Diff i

data Swap a = NoChange
            | Replace a
  deriving (Generic, Eq, Ord, Show, Read)

eqDiff :: Eq a => a -> a -> Swap a
eqDiff x y
    | x == y    = NoChange
    | otherwise = Replace y

eqPatch :: Swap a -> a -> Maybe a
eqPatch NoChange    x = Just x
eqPatch (Replace x) _ = Just x

newtype EqDiff a = EqDiff { getEqDiff :: a }
  deriving (Generic, Eq, Ord, Show, Read)

instance Patch (Swap a) where
    patchLevel NoChange    = NoDiff 1
    patchLevel (Replace _) = TotalDiff 1

    mergePatch NoChange      NoChange      = NoConflict NoChange
    mergePatch NoChange      r@(Replace _) = Conflict r
    mergePatch l@(Replace _) _             = Conflict l

instance Eq a => DefaultDiff (Swap a) a where
    defaultDiff  = eqDiff
    defaultPatch = eqPatch

instance Eq a => Diff (EqDiff a) where
    type Edit (EqDiff a) = Swap a
    diff = eqDiff `on` getEqDiff
    patch p = fmap EqDiff . eqPatch p . getEqDiff

instance (Diff a, Diff b) => Diff (a, b) where
    type Edit (a,b) = GPatchProd (a,b)

instance (Diff a, Diff b, Diff c) => Diff (a, b, c) where
    type Edit (a,b,c) = GPatchProd (a,b,c)

instance (Diff a, Diff b, Diff c, Diff d) => Diff (a, b, c, d) where
    type Edit (a,b,c,d) = GPatchProd (a,b,c,d)

instance (Diff a, Diff b, Diff c, Diff d, Diff e) => Diff (a, b, c, d, e) where
    type Edit (a,b,c,d,e) = GPatchProd (a,b,c,d,e)

instance (Diff a, Diff b, Diff c, Diff d, Diff e, Diff f) => Diff (a, b, c, d, e, f) where
    type Edit (a,b,c,d,e,f) = GPatchProd (a,b,c,d,e,f)

instance (Diff a, Diff b, Diff c, Diff d, Diff e, Diff f, Diff g) => Diff (a, b, c, d, e, f, g) where
    type Edit (a,b,c,d,e,f,g) = GPatchProd (a,b,c,d,e,f,g)

-- TODO: case w/o typeable
instance (Diff a, Diff b, Typeable a, Typeable b) => Diff (Either a b)

instance Diff Char where
    type Edit Char = Swap Char

instance Diff Bool where
    type Edit Bool = Swap Bool

instance Diff Int where
    type Edit Int = Swap Int

instance Diff Integer where
    type Edit Integer = Swap Integer

instance Diff Double where
    type Edit Double = Swap Double

instance Diff Float where
    type Edit Float = Swap Float
