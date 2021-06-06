{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , RankNTypes
  , PatternSynonyms
  , FlexibleContexts
  , FlexibleInstances
  , NoImplicitPrelude
  , UndecidableInstances
  , ScopedTypeVariables
  , ConstraintKinds
  , MultiParamTypeClasses
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Enriched
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Enriched where

import Data.Kind (Type)

import Data.Category (Category(..), Obj, Op(..))
import Data.Category.Product
import Data.Category.Functor (Functor(..), Hom(..))
import Data.Category.Limit (HasBinaryProducts(..), HasTerminalObject(..))
import Data.Category.CartesianClosed (CartesianClosed(..), ExpFunctor(..), curry, uncurry)

-- | An enriched category
class CartesianClosed (V k) => ECategory (k :: Type -> Type -> Type) where
  -- | The category V which k is enriched in
  type V k :: Type -> Type -> Type

  -- | The hom object in V from a to b
  type k $ ab :: Type
  hom :: Obj k a -> Obj k b -> Obj (V k) (k $ (a, b))

  id :: Obj k a -> Arr k a a
  comp :: Obj k a -> Obj k b -> Obj k c -> V k (BinaryProduct (V k) (k $ (b, c)) (k $ (a, b))) (k $ (a, c))


-- | Arrows as elements of @k@
type Arr k a b = V k (TerminalObject (V k)) (k $ (a, b))

compArr :: ECategory k => Obj k a -> Obj k b -> Obj k c -> Arr k b c -> Arr k a b -> Arr k a c
compArr a b c f g = comp a b c . (f &&& g)


data Underlying k a b = Underlying (Obj k a) (Arr k a b) (Obj k b)
-- | The underlying category of an enriched category
instance ECategory k => Category (Underlying k) where
  src (Underlying a _ _) = Underlying a (id a) a
  tgt (Underlying _ _ b) = Underlying b (id b) b
  Underlying b f c . Underlying a g _ = Underlying a (compArr a b c f g) c


newtype EOp k a b = EOp (k b a)
-- | The opposite of an enriched category
instance ECategory k => ECategory (EOp k) where
  type V (EOp k) = V k
  type EOp k $ (a, b) = k $ (b, a)
  hom (EOp a) (EOp b) = hom b a
  id (EOp a) = id a
  comp (EOp a) (EOp b) (EOp c) = comp c b a . (proj2 (hom c b) (hom b a) &&& proj1 (hom c b) (hom b a))


data (:<>:) :: (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type where
  (:<>:) :: (V k1 ~ V k2) => Obj k1 a1 -> Obj k2 a2 -> (:<>:) k1 k2 (a1, a2) (a1, a2)

-- | The enriched product category of enriched categories @c1@ and @c2@.
instance (ECategory k1, ECategory k2, V k1 ~ V k2) => ECategory (k1 :<>: k2) where
  type V (k1 :<>: k2) = V k1
  type (k1 :<>: k2) $ ((a1, a2), (b1, b2)) = BinaryProduct (V k1) (k1 $ (a1, b1)) (k2 $ (a2, b2))
  hom (a1 :<>: a2) (b1 :<>: b2) = hom a1 b1 *** hom a2 b2
  id (a1 :<>: a2) = id a1 &&& id a2
  comp (a1 :<>: a2) (b1 :<>: b2) (c1 :<>: c2) =
    comp a1 b1 c1 . (proj1 bc1 bc2 . proj1 l r &&& proj1 ab1 ab2 . proj2 l r) &&&
    comp a2 b2 c2 . (proj2 bc1 bc2 . proj1 l r &&& proj2 ab1 ab2 . proj2 l r)
    where
      ab1 = hom a1 b1
      ab2 = hom a2 b2
      bc1 = hom b1 c1
      bc2 = hom b2 c2
      l = bc1 *** bc2
      r = ab1 *** ab2


newtype Self v a b = Self { getSelf :: v a b }
-- | Self enrichment
instance CartesianClosed v => ECategory (Self v) where
  type V (Self v) = v
  type Self v $ (a, b) = Exponential v a b
  hom (Self a) (Self b) = ExpFunctor % (Op a :**: b)
  id (Self a) = toSelf a
  comp (Self a) (Self b) (Self c) = curry (bc *** ab) a c (apply b c . (proj1 bc ab *** apply a b) . shuffle)
    where
      bc = c ^^^ b
      ab = b ^^^ a
      shuffle = proj1 (bc *** ab) a &&& (proj2 bc ab *** a)

toSelf :: CartesianClosed v => v a b -> Arr (Self v) a b
toSelf v = curry terminalObject (src v) (tgt v) (v . proj2 terminalObject (src v))

fromSelf :: forall v a b. CartesianClosed v => Obj v a -> Obj v b -> Arr (Self v) a b -> v a b
fromSelf a b arr = uncurry terminalObject a b arr . (terminate a &&& a)


newtype InHask k a b = InHask (k a b)
-- | Any regular category is enriched in (->), aka Hask
instance Category k => ECategory (InHask k) where
  type V (InHask k) = (->)
  type InHask k $ (a, b) = k a b
  hom (InHask a) (InHask b) = Hom % (Op a :**: b)
  id (InHask f) () = f
  comp _ _ _ (f, g) = f . g
