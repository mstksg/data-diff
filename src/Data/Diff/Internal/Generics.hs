{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}


module Data.Diff.Internal.Generics (
    SumDiff(..)
  , CtrDiff(..)
  , diffSOP
  , diffSOP'
  , patchSOP
  , undiffSOP
  , showSOP
  , showProd
  ) where

import           Control.Monad
import           Data.Bifunctor
import           Data.Diff.Pretty
import           Data.Kind
import           Data.Maybe
import           Data.Type.Combinator
import           Data.Type.Combinator.Util
import           Data.Type.Conjunction
import           Data.Type.Equality
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Reflection
import qualified Data.Type.Product            as TCP
import qualified Data.Type.Sum                as TCS
import qualified Generics.SOP                 as SOP
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data SumDiff :: (k -> Type) -> (k -> Type) -> [k] -> Type where
    SD :: (Index as :&: CtrDiff f g as) a -> SumDiff f g as

data CtrDiff :: (k -> Type) -> (k -> Type) -> [k] -> k -> Type where
    CDEdit :: g a -> CtrDiff f g as a
    CDName :: (Index as :&: g) a -> CtrDiff f g as a
    CDDiff :: f a -> (Index as :&: f) b -> CtrDiff f g as a

-- | Version of 'sumDiff'' that treats constructor changes as total edits
-- even if the contents have the same type
sumDiff'
    :: forall f g as. ()
    => (forall a. (Index as :&: f :&: f) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff' f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
    case testEquality i j of
      Just Refl -> SD ( i :&: CDEdit (f (i :&: x :&: y)) )
      Nothing   -> SD ( i :&: CDDiff x (j :&: y)  )

-- | Version of 'sumDiff' that treats constructor changes as partial edits
-- if the contents have the same type
sumDiff
    :: forall f g as. Every Typeable as
    => (forall a. Typeable a => ((Index as :&: f) :&: (Index as :&: f)) a -> g a)
    -> Sum f as
    -> Sum f as
    -> SumDiff f g as
sumDiff f (sumIx -> Some (i :&: x)) (sumIx -> Some (j :&: y)) =
        every @_ @Typeable i //
        every @_ @Typeable j //
    case testEquality (tr i) (tr j) of
      Just Refl
        | i == j    -> SD ( i
                        :&: CDEdit (f ((i :&: x) :&: (j :&: y)))
                          )
        | otherwise -> SD ( i
                        :&: CDName (j :&: f ((i :&: x) :&: (j :&: y)))
                          )
      Nothing   -> SD ( i :&: CDDiff x (j :&: y) )
  where
    tr :: Typeable a => p a -> TypeRep a
    tr _ = typeRep

diffSOP'
    :: forall f ass. ()
    => (forall as a. Index ass as -> Index as a -> a -> a -> f a)
    -> Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod f) ass
diffSOP' f = sumDiff' combine
  where
    combine
        :: forall as. ()
        => (Index ass :&: Tuple :&: Tuple) as
        -> Prod f as
    combine (i :&: xs :&: ys) = izipProdWith go xs ys
      where
        go :: Index as a -> I a -> I a -> f a
        go j (I x) (I y) = f i j x y

diffSOP
    :: forall f ass. (Every Typeable ass)
    => (forall as a. Index ass as -> Index as a -> a -> a -> f a)   -- ^ diff
    -> Sum Tuple ass
    -> Sum Tuple ass
    -> SumDiff Tuple (Prod f) ass
diffSOP f = sumDiff combine
  where
    combine
        :: forall as. ()
        => ((Index ass :&: Tuple) :&: (Index ass :&: Tuple)) as
        -> Prod f as
    combine ((i :&: xs) :&: (_ :&: ys)) = izipProdWith go xs ys
      where
        go :: Index as a -> I a -> I a -> f a
        go j (I x) (I y) = f i j x y

patchSOP
    :: forall f ass. ()
    => (forall as a. Index ass as -> Index as a -> f a -> a -> Maybe a)     -- ^ patch
    -> (forall as a. Index ass as -> Index as a -> a -> a -> Bool)          -- ^ eq
    -> SumDiff Tuple (Prod f) ass
    -> Sum Tuple ass
    -> Maybe (Sum Tuple ass)
patchSOP f g = \case
    SD (i :&: CDEdit es) -> \xss -> do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go i k) (zipProd es xs)
      return (injectSum i ys)
    SD (i :&: CDName (j :&: es)) -> \xss -> do
      xs <- TCS.index i xss
      ys <- itraverse1 (\k -> fmap I . go i k) (zipProd es xs)
      return (injectSum j ys)
    SD (i :&: CDDiff xs (j :&: ys)) -> \xss -> do
      xs' <- TCS.index i xss            -- TODO: should this be verified?
      izipProdWithA_ (\k (I x') (I x) -> guard $ g i k x' x) xs' xs
      return (injectSum j ys)
  where
    go  :: Index ass as -> Index as a -> (f :&: I) a -> Maybe a
    go i k (e :&: I x) = f i k e x

undiffSOP
    :: (forall as a. Index ass as -> Index as a -> f a -> (a, a))
    -> SumDiff Tuple (Prod f) ass
    -> (Sum Tuple :&: Sum Tuple) ass
undiffSOP f (SD (i :&: cd)) = case cd of
    CDEdit es -> (injectSum i .&. injectSum i)
               . unzipProd
               . imap1 (\j e -> let (x, y) = f i j e
                                in  I x :&: I y
                       )
               $ es
    CDName (j :&: es) -> (injectSum i .&. injectSum j)
                       . unzipProd
                       . imap1 (\k e -> let (x, y) = f i k e
                                        in  I x :&: I y
                               )
                       $ es
    CDDiff xs (j :&: ys) -> injectSum i xs :&: injectSum j ys

showSOP
    :: forall f ass. (Every (Every Show) ass)
    => (forall as a. Index ass as -> Index as a -> f a -> Maybe PP.Doc)
    -> SOP.DatatypeInfo ass
    -> SumDiff Tuple (Prod f) ass
    -> PP.Doc
showSOP f di (SD ((i :: Index ass as) :&: cd)) = case cd of
    CDEdit es ->
      let ds = ifoldMap1 (\j -> (:[]) . f i j) es
      in  if null (catMaybes ds)
            then ppNoChange
            else (iNm PP.<+>) . PP.align $ case iCtr of
              SOP.Constructor{} -> docList ds
              SOP.Infix{}       -> docList ds
              SOP.Record{}      ->
                recDoc $ catMaybes (zipWith (fmap . recField) iFs ds)
    CDName ((j :: Index ass bs) :&: es) ->
      let ds = ifoldMap1 (\k -> (:[]) . f i k) es
          jCtr :: SOP.ConstructorInfo bs
          jCtr = ctrInfo j
          (jNm, jFs) = bimap PP.text (TCP.toList SOP.fieldName) . ctrNames $ jCtr
      in  (ppDel iNm PP.<$>) . (ppAdd jNm PP.<+>) . PP.align $ if null ds
            then mempty
            else case (iCtr, jCtr) of
                  (_           , SOP.Record{}) ->
                    recDoc $ catMaybes (zipWith3 editsCR iFs jFs ds)
                  (SOP.Record{}, _           ) ->
                    recDoc $ catMaybes (zipWith3 editsCR iFs jFs ds)
                  (_           , _           ) -> docList ds
    CDDiff _ ((j :: Index ass bs) :&: ys) ->
      let jCtr :: SOP.ConstructorInfo bs
          jCtr = ctrInfo j
          (jNm, jFs) = bimap PP.text (TCP.toList SOP.fieldName) . ctrNames $ jCtr
          ds = ifoldMap1 (\k (I x) -> [PP.text (show x)]
                                        \\ every @_ @Show k
                                        \\ every @_ @(Every Show) j
                         )
                 ys
      in  (ppDel iNm PP.<$>) . (ppAdd jNm PP.<+>) . PP.align $ case jCtr of
            SOP.Constructor{} -> PP.vcat ds
            SOP.Infix{}       -> PP.vcat ds
            SOP.Record{}      -> recDoc $ zipWith recField jFs ds
  where
    ctrInfo :: Index ass bs -> SOP.ConstructorInfo bs
    ctrInfo j = TCP.index j . sopProd . SOP.constructorInfo $ di
    iCtr :: SOP.ConstructorInfo as
    iCtr = TCP.index i . sopProd $ SOP.constructorInfo di
    (iNm, iFs) = bimap PP.text (TCP.toList SOP.fieldName) . ctrNames $ iCtr
    editsCR :: SOP.FieldName -> SOP.FieldName -> Maybe PP.Doc -> Maybe PP.Doc
    editsCR f1 f2 = fmap $ \e -> PP.text f1
                          PP.<+> PP.yellow (PP.text "~>")
                          PP.<+> PP.text f2
                          PP.<+> e

showProd
    :: (forall a. Index as a -> f a -> Maybe PP.Doc)
    -> SOP.ConstructorInfo as
    -> Prod f as
    -> PP.Doc
showProd f ci es
  | null (catMaybes ds) = ppNoChange
  | otherwise           = iNm PP.<+> case ci of
      SOP.Constructor{} -> docList ds
      SOP.Infix{}       -> docList ds
      SOP.Record{}      ->
        recDoc $ catMaybes (zipWith (fmap . recField) iFs ds)
  where
    ds = ifoldMap1 (\i -> (:[]) . f i) es
    (iNm, iFs) = bimap PP.text (TCP.toList SOP.fieldName) . ctrNames $ ci


recDoc :: [PP.Doc] -> PP.Doc
recDoc = PP.encloseSep PP.lbrace PP.rbrace PP.comma
recField :: SOP.FieldName -> PP.Doc -> PP.Doc
recField fn d = PP.text fn PP.<+> PP.char '=' PP.<+> d
docList :: [Maybe PP.Doc] -> PP.Doc
docList = PP.vcat . map (fromMaybe ppNoChange)

ctrNames
    :: forall as. ()
    => SOP.ConstructorInfo as
    -> (String, Prod SOP.FieldInfo as)
ctrNames = \case
    SOP.Constructor n -> (n, numeric)   \\ sListLength (SOP.sList @_ @as)
    SOP.Infix n _ _   -> ("(_ " ++ n ++ " _)", numeric)
    SOP.Record n fs   -> (n, sopProd fs)
  where
    numeric :: forall bs. Known Length bs => Prod SOP.FieldInfo bs
    numeric = map1 (SOP.FieldInfo . show . ixNum) indices

