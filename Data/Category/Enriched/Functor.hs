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
-- Module      :  Data.Category.Enriched.Functor
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Enriched.Functor where

import Data.Kind (Type)

import Data.Category (Category(..), Obj)
import Data.Category.Functor (Functor(..))
import Data.Category.Limit (HasBinaryProducts(..), HasTerminalObject(..))
import Data.Category.CartesianClosed
import Data.Category.Enriched

-- | Enriched functors.
class (ECategory (EDom ftag), ECategory (ECod ftag), V (EDom ftag) ~ V (ECod ftag)) => EFunctor ftag where

  -- | The domain, or source category, of the functor.
  type EDom ftag :: Type -> Type -> Type
  -- | The codomain, or target category, of the functor.
  type ECod ftag :: Type -> Type -> Type

  -- | @:%%@ maps objects at the type level
  type ftag :%% a :: Type

  -- | @%%@ maps object at the value level
  (%%) :: ftag -> Obj (EDom ftag) a -> Obj (ECod ftag) (ftag :%% a)

  -- | `map` maps arrows.
  map :: (EDom ftag ~ k) => ftag -> Obj k a -> Obj k b -> V k (k $ (a, b)) (ECod ftag $ (ftag :%% a, ftag :%% b))

type EFunctorOf a b t = (EFunctor t, EDom t ~ a, ECod t ~ b)


data Id (k :: Type -> Type -> Type) = Id
-- | The identity functor on k
instance ECategory k => EFunctor (Id k) where
  type EDom (Id k) = k
  type ECod (Id k) = k
  type Id k :%% a = a
  Id %% a = a
  map Id = hom

data (g :.: h) where
  (:.:) :: (EFunctor g, EFunctor h, ECod h ~ EDom g) => g -> h -> g :.: h
-- | The composition of two functors.
instance (ECategory (ECod g), ECategory (EDom h), V (EDom h) ~ V (ECod g), ECod h ~ EDom g) => EFunctor (g :.: h) where
  type EDom (g :.: h) = EDom h
  type ECod (g :.: h) = ECod g
  type (g :.: h) :%% a = g :%% (h :%% a)
  (g :.: h) %% a = g %% (h %% a)
  map (g :.: h) a b = map g (h %% a) (h %% b) . map h a b

data Const (c1 :: Type -> Type -> Type) (c2 :: Type -> Type -> Type) x where
  Const :: Obj c2 x -> Const c1 c2 x
-- | The constant functor.
instance (ECategory c1, ECategory c2, V c1 ~ V c2) => EFunctor (Const c1 c2 x) where
  type EDom (Const c1 c2 x) = c1
  type ECod (Const c1 c2 x) = c2
  type Const c1 c2 x :%% a = x
  Const x %% _ = x
  map (Const x) a b = id x . terminate (hom a b)

data Opposite f where
  Opposite :: EFunctor f => f -> Opposite f
-- | The dual of a functor
instance (EFunctor f) => EFunctor (Opposite f) where
  type EDom (Opposite f) = EOp (EDom f)
  type ECod (Opposite f) = EOp (ECod f)
  type Opposite f :%% a = f :%% a
  Opposite f %% EOp a = EOp (f %% a)
  map (Opposite f) (EOp a) (EOp b) = map f b a

data f1 :<*>: f2 = f1 :<*>: f2
-- | @f1 :<*>: f2@ is the product of the functors @f1@ and @f2@.
instance (EFunctor f1, EFunctor f2, V (ECod f1) ~ V (ECod f2)) => EFunctor (f1 :<*>: f2) where
  type EDom (f1 :<*>: f2) = EDom f1 :<>: EDom f2
  type ECod (f1 :<*>: f2) = ECod f1 :<>: ECod f2
  type (f1 :<*>: f2) :%% (a1, a2) = (f1 :%% a1, f2 :%% a2)
  (f1 :<*>: f2) %% (a1 :<>: a2) = (f1 %% a1) :<>: (f2 %% a2)
  map (f1 :<*>: f2) (a1 :<>: a2) (b1 :<>: b2) = map f1 a1 b1 *** map f2 a2 b2

data DiagProd (k :: Type -> Type -> Type) = DiagProd
-- | 'DiagProd' is the diagonal functor for products.
instance ECategory k => EFunctor (DiagProd k) where
  type EDom (DiagProd k) = k
  type ECod (DiagProd k) = k :<>: k
  type DiagProd k :%% a = (a, a)
  DiagProd %% a = a :<>: a
  map DiagProd a b = hom a b &&& hom a b

newtype UnderlyingF f = UnderlyingF f
-- | The underlying functor of an enriched functor @f@
instance EFunctor f => Functor (UnderlyingF f) where
  type Dom (UnderlyingF f) = Underlying (EDom f)
  type Cod (UnderlyingF f) = Underlying (ECod f)
  type UnderlyingF f :% a = f :%% a
  UnderlyingF f % Underlying a ab b = Underlying (f %% a) (map f a b . ab) (f %% b)

newtype InHaskF f = InHaskF f
-- | A regular functor is a functor enriched in Hask.
instance Functor f => EFunctor (InHaskF f) where
  type EDom (InHaskF f) = InHask (Dom f)
  type ECod (InHaskF f) = InHask (Cod f)
  type InHaskF f :%% a = f :% a
  InHaskF f %% InHask a = InHask (f % a)
  map (InHaskF f) _ _ = \g -> f % g

newtype InHaskToHask f = InHaskToHask f
instance (Functor f, Cod f ~ (->)) => EFunctor (InHaskToHask f) where
  type EDom (InHaskToHask f) = InHask (Dom f)
  type ECod (InHaskToHask f) = Self (->)
  type InHaskToHask f :%% a = f :% a
  InHaskToHask f %% InHask a = Self (f % a)
  map (InHaskToHask f) _ _ = \g -> f % g

newtype UnderlyingHask (c :: Type -> Type -> Type) (d :: Type -> Type -> Type) f = UnderlyingHask f
-- | The underlying functor of an enriched functor @f@ enriched in Hask.
instance (EFunctor f, EDom f ~ InHask c, ECod f ~ InHask d, Category c, Category d) => Functor (UnderlyingHask c d f) where
  type Dom (UnderlyingHask c d f) = c
  type Cod (UnderlyingHask c d f) = d
  type UnderlyingHask c d f :% a = f :%% a
  UnderlyingHask f % g = map f (InHask (src g)) (InHask (tgt g)) g

data EHom (k :: Type -> Type -> Type) = EHom
instance ECategory k => EFunctor (EHom k) where
  type EDom (EHom k) = EOp k :<>: k
  type ECod (EHom k) = Self (V k)
  type EHom k :%% (a, b) = k $ (a, b)
  EHom %% (EOp a :<>: b) = Self (hom a b)
  map EHom (EOp a1 :<>: a2) (EOp b1 :<>: b2) = curry (ba *** ab) a b (comp b1 a1 b2 . (comp a1 a2 b2 . (proj2 ba ab *** a) &&& proj1 ba ab . proj1 (ba *** ab) a))
    where
      a = hom a1 a2
      b = hom b1 b2
      ba = hom b1 a1
      ab = hom a2 b2

-- | The enriched functor @k(x, -)@
data EHomX_ k x = EHomX_ (Obj k x)
instance ECategory k => EFunctor (EHomX_ k x) where
  type EDom (EHomX_ k x) = k
  type ECod (EHomX_ k x) = Self (V k)
  type EHomX_ k x :%% y = k $ (x, y)
  EHomX_ x %% y = Self (hom x y)
  map (EHomX_ x) a b = curry (hom a b) (hom x a) (hom x b) (comp x a b)

-- | The enriched functor @k(-, x)@
data EHom_X k x = EHom_X (Obj (EOp k) x)
instance ECategory k => EFunctor (EHom_X k x) where
  type EDom (EHom_X k x) = EOp k
  type ECod (EHom_X k x) = Self (V k)
  type EHom_X k x :%% y = k $ (y, x)
  EHom_X x %% y = Self (hom x y)
  map (EHom_X x) a b = curry (hom a b) (hom x a) (hom x b) (comp x a b)


-- | A V-enrichment on a functor @F: V -> V@ is the same thing as tensorial strength @(a, f b) -> f (a, b)@.
strength :: EFunctorOf (Self v) (Self v) f => f -> Obj v a -> Obj v b -> v (BinaryProduct v a (f :%% b)) (f :%% (BinaryProduct v a b))
strength f a b = uncurry a fb fab (map f (Self b) (Self (a *** b)) . tuple b a)
  where
    Self fb = f %% Self b
    Self fab = f %% Self (a *** b)


-- | Enriched natural transformations.
data ENat :: (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type where
  ENat :: (EFunctorOf c d f, EFunctorOf c d g)
    => f -> g -> (forall z. Obj c z -> Arr d (f :%% z) (g :%% z)) -> ENat c d f g
