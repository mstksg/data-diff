{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
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
  , merge, catLevels, normDL, dlPercent, percentDiff, prodPatchLevel
  , compareDiff
  , ShowPatch(..)
  , DefaultDiff(..)
  , Edit'(..), diff', patch', undiff'
  , Swap(..), eqDiff, eqPatch
  , EqDiff(..)
  , gpatchLevel
  , gmergePatch
  , GPatch(..), GPatch'(..)
  , gdiff
  , gdiff'
  , gpatch
  , gundiff
  , GPatchProd(..)
  , gdiffProd
  , gpatchProd
  , gundiffProd
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Internal.Generics
import           Data.Diff.Pretty
import           Data.Foldable
import           Data.Function
import           Data.Maybe
import           Data.Proxy
import           Data.Semigroup               (Semigroup(..))
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Product hiding     (toList)
import           Data.Type.Sum
import           GHC.Generics                 (Generic)
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Reflection
import qualified Generics.SOP                 as SOP
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- | Data type representing a "percentage difference"
data DiffLevel = DL { dlAmt :: Double
                    , dlTot :: Double
                    }
  deriving Show

instance Semigroup DiffLevel where
    DL x s <> DL y t = DL (x + y) (s + t)

instance Monoid DiffLevel where
    mappend = (<>)
    mempty  = DL 0 0

-- | Is the 'DiffLevel' a no difference?
noDiff :: DiffLevel -> Maybe Double
noDiff (DL y t)
    | abs y <= 0.0001 = Just t
    | otherwise       = Nothing

pattern NoDiff :: Double -> DiffLevel
pattern NoDiff t <- (noDiff->Just t)
  where
    NoDiff t = DL 0 t

-- | Is the 'DiffLevel' a total difference?
totalDiff :: DiffLevel -> Maybe Double
totalDiff (DL y t)
  | abs (y - t) < 0.0001 = Just t
  | otherwise            = Nothing

pattern TotalDiff :: Double -> DiffLevel
pattern TotalDiff t <- (totalDiff->Just t)
  where
    TotalDiff t = DL t t

-- | Rescale 'DiffLevel' to be out of a given total.
normDL :: Double -> DiffLevel -> Maybe DiffLevel
normDL s (DL x t)
    | t == 0    = Nothing
    | otherwise = Just $ DL (x / t * s) s

-- | Calculate percent difference.
--
-- TODO: What about 0?
dlPercent :: DiffLevel -> Double
dlPercent (DL x t) = x / t

-- | Merge all 'DiffLevel' in a 'Foldable' container, treating them all as
-- equally weighted.
catLevels
    :: Foldable f
    => f DiffLevel
    -> DiffLevel
catLevels xs = case normed of
    [] | null xs   -> NoDiff 1
       | otherwise -> NoDiff (fromIntegral (length xs))
    ds -> fold ds
  where
    normed = mapMaybe (normDL 1) . toList $ xs


-- | Result of a merge
data MergeResult a = Incompatible       -- ^ Incompatible sources
                   | Conflict   a       -- ^ Conflicts, throwing away info
                   | NoConflict a       -- ^ All conflicts resolved
  deriving (Functor, Show, Eq, Ord, Foldable, Traversable)

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

class Patch a => ShowPatch a where
    showPatch :: a -> PP.Doc

-- | Diffable types
--
-- @
-- 'uncurry' 'diff' . 'undiff' = 'id'
-- 'undiff' . 'uncurry' 'diff' = 'id'
-- 'patch' ('diff' x y) x = 'Just' y
-- @
class (Eq a, Patch (Edit a)) => Diff a where
    type Edit a
    type instance Edit a = GPatch a
    -- | Generate a patch between two values, that can be used to transform
    -- one value into the other
    diff      :: a -> a -> Edit a
    -- | Apply a patch to a value
    patch     :: Edit a -> a -> Maybe a
    -- | Deconstruct a patch to recover the original value used to create
    -- it, and the application of the patch to that original value
    undiff    :: Edit a -> (a, a)

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

    default undiff
        :: DefaultDiff (Edit a) a
        => Edit a
        -> (a, a)
    undiff = defaultUndiff


class DefaultDiff p a where
    defaultDiff   :: a -> a -> p
    defaultPatch  :: p -> a -> Maybe a
    defaultUndiff :: p -> (a, a)

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every Typeable (SOP.Code a))
      => DefaultDiff (GPatch a) a where
    defaultDiff   = gdiff
    defaultPatch  = gpatch
    defaultUndiff = gundiff

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a))
      => DefaultDiff (GPatch' a) a where
    defaultDiff x = GP' . gdiff' x
    defaultPatch  = gpatch . getGP'
    defaultUndiff = gundiff . getGP'


-- | Left-biased merge of two diffable values.
merge :: Diff a => a -> a -> a -> MergeResult a
merge o x y = do
    pz <- mergePatch px py
    maybe Incompatible NoConflict $ patch pz o
  where
    px = diff o x
    py = diff o y

-- | Newtype used to get around partial application of type families
newtype Edit' a = Edit' { getEdit' :: Edit a }
    deriving (Generic)

instance SOP.Generic (Edit' a)
instance Patch (Edit a) => Patch (Edit' a)
instance ShowPatch (Edit a) => ShowPatch (Edit' a) where
    showPatch = showPatch . getEdit'

-- | 'diff'' lifted to 'Edit''
diff' :: Diff a => a -> a -> Edit' a
diff' x y = Edit' (diff x y)

-- | 'patch'' lifted to 'Edit''
patch' :: Diff a => Edit' a -> a -> Maybe a
patch' (Edit' e) = patch e

-- | 'undiff'' lifted to 'Edit''
undiff' :: Diff a => Edit' a -> (a, a)
undiff' (Edit' e) = undiff e

-- | How different two items are, as a percentage
percentDiff :: Diff a => a -> a -> Double
percentDiff x = dlPercent . compareDiff x

-- | Get 'DiffLevel' between two items
compareDiff :: Diff a => a -> a -> DiffLevel
compareDiff x y = patchLevel (diff x y)

-- | 'patchLevel' written to work for any types deriving 'SOP.Generic'.
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

-- | 'mergePatch' written to work for any __product types__ deriving
-- 'SOP.Generic'.
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


-- | Generic patch type for any types deriving 'SOP.Generic'.
newtype GPatch a = GP { getGP :: SumDiff Tuple (Prod Edit') (SOP.Code a) }
  deriving (Generic)

instance SOP.Generic (GPatch a)

-- | Newtype wrapper over 'GPatch' to give alternative 'DefaultDiff'
-- instance, which treats all constructor changes as total differences,
-- even if they have the same type of values.
newtype GPatch' a = GP' { getGP' :: GPatch a }

instance ( SOP.Generic a
        , Every (Every Diff) (SOP.Code a)
        )
        => Patch (GPatch a) where
    patchLevel = gpPatchLevel
    mergePatch = gpMergePatch

instance ( SOP.Generic a
         , SOP.HasDatatypeInfo a
         , Every (Every Diff) (SOP.Code a)
         , Every (Every Show) (SOP.Code a)
         , Every (Every (Comp ShowPatch Edit')) (SOP.Code a)
         )
        => ShowPatch (GPatch a) where
    showPatch = gpShowPatch

instance (SOP.Generic a, Every (Every Diff) (SOP.Code a))
        => Patch (GPatch' a) where
    patchLevel = gpPatchLevel . getGP'
    mergePatch x y = GP' <$> gpMergePatch (getGP' x) (getGP' y)

instance ( SOP.Generic a
         , SOP.HasDatatypeInfo a
         , Every (Every Diff) (SOP.Code a)
         , Every (Every Show) (SOP.Code a)
         , Every (Every (Comp ShowPatch Edit')) (SOP.Code a)
         )
        => ShowPatch (GPatch' a) where
    showPatch = gpShowPatch . getGP'

-- | Patch level for 'GPatch'
gpPatchLevel
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> DiffLevel
gpPatchLevel (GP (SD (i :&: cd))) = case cd of
    CDEdit es         -> prodPatchLevel es \\ every @_ @(Every Diff) i
    CDName (_ :&: es) -> TotalDiff 1 <> prodPatchLevel es
                                      \\ every @_ @(Every Diff) i
    CDDiff _ _        -> TotalDiff 1

-- | 'DiffLevel' of a 'Prod' of 'Edit's
prodPatchLevel :: forall as. Every Diff as => Prod Edit' as -> DiffLevel
prodPatchLevel = catLevels . ifoldMap1 go
  where
    go :: Index as a -> Edit' a -> [DiffLevel]
    go i (Edit' e) = [patchLevel e] \\ every @_ @Diff i

prodShowPatch
    :: (Every Diff as, Every (Comp ShowPatch Edit') as)
    => SOP.ConstructorInfo as
    -> Prod Edit' as
    -> PP.Doc
prodShowPatch = showProd $ \i e -> every @_ @Diff i //
                                   every @_ @(Comp ShowPatch Edit') i //
    case patchLevel e of
      NoDiff _ -> Nothing
      _        -> Just $ showPatch e

-- | Merge 'GPatch'
gpMergePatch
    :: (Every (Every Diff) (SOP.Code a), Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> GPatch a
    -> MergeResult (GPatch a)
gpMergePatch (GP (SD (i1 :&: cd1)))
             (GP (SD (i2 :&: cd2)))
        = every @_ @(Every Diff) i1 //
          GP . SD . (i1 :&:) <$> case testEquality i1 i2 of
    Just Refl -> case cd1 of
      CDEdit es1 -> case cd2 of
        CDEdit es2 -> CDEdit <$> prodMergePatch es1 es2
        CDName (j2 :&: es2) -> CDName . (j2 :&:) <$> prodMergePatch es1 es2
        CDDiff _ _ -> case prodPatchLevel es1 of
          NoDiff _ -> NoConflict cd2
          _        -> Conflict cd1
      CDName (j1 :&: es1) -> case cd2 of
        CDEdit es2 -> CDName . (j1 :&:) <$> prodMergePatch es1 es2
        CDName (j2 :&: es2) -> do
          case testEquality j1 j2 of
            Just Refl -> NoConflict ()
            Nothing   -> Conflict   ()
          CDName . (j1 :&:) <$> prodMergePatch es1 es2
        CDDiff _ (_ :&: _) -> Conflict cd2
      CDDiff os (j1 :&: xs) -> case cd2 of
        CDEdit es2 -> case prodPatchLevel es2 of
          NoDiff _ -> NoConflict cd1
          _        -> Conflict cd1
        CDName _ -> Conflict cd1
        CDDiff os' (j2 :&: ys) -> do
          izipProdWithA_ (\k o' o -> unless (o == o') Incompatible
                              \\ every @_ @Diff k
                         ) os' os
          case testEquality j1 j2 of
            Just Refl -> do
              zs <- izipProdWithA (\i (I x) (I y) ->
                                      I <$> if x == y \\ every @_ @Diff i
                                        then NoConflict x
                                        else Conflict   x
                                  )
                      xs
                      ys     \\ every @_ @(Every Diff) j1
              pure (CDDiff os (j1 :&: zs))
            Nothing -> Conflict cd1
    Nothing   -> Incompatible

gpShowPatch
    :: forall a. (Every (Every Show) (SOP.Code a), Every (Every (Comp ShowPatch Edit')) (SOP.Code a), SOP.HasDatatypeInfo a)
    => GPatch a -> PP.Doc
gpShowPatch (GP es) = showSOP (\i j e ->
                                  (case patchLevel e of
                                    NoDiff _ -> Nothing
                                    _        -> Just (showPatch e))
                                      \\ every @_ @Show j
                                      \\ every @_ @(Every Show) i
                                      \\ every @_ @(Comp ShowPatch Edit') j
                                      \\ every @_ @(Every (Comp ShowPatch Edit')) i
                              )
                        (SOP.datatypeInfo (Proxy @a))
                        es

-- | Merge product of patches
prodMergePatch
    :: forall as. Every Diff as
    => Prod Edit' as
    -> Prod Edit' as
    -> MergeResult (Prod Edit' as)
prodMergePatch = izipProdWithA go
  where
    go  :: Index as a
        -> Edit' a
        -> Edit' a
        -> MergeResult (Edit' a)
    go i x y = mergePatch x y \\ every @_ @Diff i

-- | 'diff' intented to work for all instances of 'SOP.Generic'.  Differs
-- from 'gdiff' in that it treats constructor changes as total differences,
-- even if they both contain the same type of values.
gdiff'
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
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

-- | 'diff' intented to work for all instances of 'SOP.Generic'.  Will
-- treat constructor changes as partial differences if they both contain
-- the same type of values.
gdiff
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a), Every Typeable (SOP.Code a))
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


-- | 'patch' intented to work for all instances of 'SOP.Generic'.
gpatch
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> a
    -> Maybe a
gpatch e = fmap (SOP.to . sopSop . map1 (map1 (SOP.I . getI)))
         . patchSOP p q (getGP e)
         . map1 (map1 (I . SOP.unI))
         . sopSOP
         . SOP.from
  where
    p :: Index (SOP.Code a) as -> Index as b -> Edit' b -> b -> Maybe b
    p i j = patch' \\ every @_ @Diff         j
                   \\ every @_ @(Every Diff) i
    q :: Index (SOP.Code a) as -> Index as b -> b -> b -> Bool
    q i j = (==)   \\ every @_ @Diff j
                   \\ every @_ @(Every Diff) i

-- | 'undiff' intended to work for all instances of 'SOP.Generic'.
gundiff
    :: forall a. (SOP.Generic a, Every (Every Diff) (SOP.Code a))
    => GPatch a
    -> (a, a)
gundiff = (\(xs :&: ys) -> (go xs, go ys))
        . undiffSOP p
        . getGP
  where
    p :: Index (SOP.Code a) as -> Index as b -> Edit' b -> (b, b)
    p i j = undiff' \\ every @_ @Diff         j
                    \\ every @_ @(Every Diff) i
    go :: Sum Tuple (SOP.Code a) -> a
    go = SOP.to . sopSop . map1 (map1 (SOP.I . getI))


-- | Generic patch type for all product types that are instances of
-- 'SOP.Generic'.
data GPatchProd a = forall as. (SOP.Code a ~ '[as])
                 => GPP { getGPP :: Prod Edit' as }

instance (SOP.IsProductType a as, Every Diff as) => Patch (GPatchProd a) where
    patchLevel (GPP es) = prodPatchLevel es
    mergePatch (GPP es1) (GPP es2) = GPP <$> prodMergePatch es1 es2

instance ( SOP.IsProductType a as
         , Every Diff as
         , Every Show as
         , SOP.HasDatatypeInfo a
         , Every (Comp ShowPatch Edit') as
         ) => ShowPatch (GPatchProd a) where
    showPatch (GPP es) = prodShowPatch
        (SOP.hd . SOP.constructorInfo . SOP.datatypeInfo $ Proxy @a)
        es

instance (SOP.IsProductType a as, Every Diff as) => DefaultDiff (GPatchProd a) a where
    defaultDiff   = gdiffProd
    defaultPatch  = gpatchProd
    defaultUndiff = gundiffProd

-- | 'diff' intended to work for all product types that are instances of
-- 'SOP.Generic'.
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

-- | 'patch' intended to work for all product types that are instances of
-- 'SOP.Generic'.
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

-- | 'undiff' intended to work for all product types that are instances of
-- 'SOP.Generic'.
gundiffProd
    :: forall a as. (SOP.IsProductType a as, Every Diff as)
    => GPatchProd a
    -> (a, a)
gundiffProd (GPP es) = (\(xs :&: ys) -> (unsop xs, unsop ys))
                     . unzipProd
                     . imap1 go
                     $ es
  where
    go :: Index as b -> Edit' b -> (I :&: I) b
    go i e = I x :&: I y
      where
        (x, y) = undiff' e \\ every @_ @Diff i
    unsop :: Tuple as -> a
    unsop = SOP.to . SOP.SOP . SOP.Z . prodSOP . map1 (SOP.I . getI)

-- | Patch type that treats all changes as total differences
data Swap a = NoChange a
            | Replace a a
  deriving (Generic, Eq, Ord, Show, Read)

-- | 'diff' for all instances of 'Eq'
eqDiff :: Eq a => a -> a -> Swap a
eqDiff x y
    | x == y    = NoChange x
    | otherwise = Replace x y

-- | 'patch' for 'Swap'
eqPatch :: Swap a -> a -> Maybe a
eqPatch (NoChange _ ) x = Just x
eqPatch (Replace _ x) _ = Just x

eqUndiff :: Swap a -> (a, a)
eqUndiff (NoChange x)  = (x,x)
eqUndiff (Replace x y) = (x,y)

-- | Newtype wrapper that gives an automatic 'Diff' instance that treats
-- all changes as total differences.
newtype EqDiff a = EqDiff { getEqDiff :: a }
  deriving (Generic, Eq, Ord, Show, Read)

instance Eq a => Patch (Swap a) where
    patchLevel (NoChange _)  = NoDiff 1
    patchLevel (Replace _ _) = TotalDiff 1

    mergePatch (NoChange x)    (NoChange y)
      | x == y    = NoConflict (NoChange x)
      | otherwise = Incompatible                -- TODO: be more lenient?
    mergePatch (NoChange _)    r@(Replace _ _) = Conflict r
    mergePatch l@(Replace _ _) _               = Conflict l

instance Eq a => DefaultDiff (Swap a) a where
    defaultDiff   = eqDiff
    defaultPatch  = eqPatch
    defaultUndiff = eqUndiff

instance (Show a, Eq a) => ShowPatch (Swap a) where
    showPatch (NoChange _ ) = ppNoChange
    showPatch (Replace x y) = ppDel (PP.text (show x))
                       PP.</> ppAdd (PP.text (show y))

instance Eq a => Diff (EqDiff a) where
    type Edit (EqDiff a) = Swap a
    diff    = eqDiff `on` getEqDiff
    patch p = fmap EqDiff . eqPatch p . getEqDiff
    undiff  = bimap EqDiff EqDiff . eqUndiff

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
