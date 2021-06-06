{-# LANGUAGE TypeOperators, RankNTypes, GADTs, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.WeightedLimit
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.WeightedLimit where

import Data.Kind (Type)

import Data.Category
import Data.Category.Functor
import Data.Category.Product
import Data.Category.NaturalTransformation
import qualified Data.Category.Limit as L


-- | @w@-weighted limits in the category @k@.
class (Functor w, Cod w ~ (->), Category k) => HasWLimits k w where
  type WeightedLimit k w d :: Type
  limitObj :: FunctorOf (Dom w) k d => w -> d -> Obj k (WLimit w d)
  limit :: FunctorOf (Dom w) k d => w -> d -> Obj (Dom w) a -> w :% a -> k (WLimit w d) (d :% a)
  limitFactorizer :: FunctorOf (Dom w) k d => w -> d -> Obj k e -> (forall a. Obj (Dom w) a -> w :% a -> k e (d :% a)) -> k e (WLimit w d)

type WLimit w d = WeightedLimit (Cod d) w d

-- | Regular limits as weigthed limits, weighted by the constant functor to '()'.
instance L.HasLimits j k => HasWLimits k (Const j (->) ()) where
  type WeightedLimit k (Const j (->) ()) d = L.Limit d
  limitObj (Const _) d = L.coneVertex (L.limit (natId d))
  limit (Const _) d a () = L.limit (natId d) ! a
  limitFactorizer (Const _) d e f = L.limitFactorizer (Nat (Const e) d (`f` ()))


class Category v => HasEnds v where
  type End (v :: Type -> Type -> Type) t :: Type
  end :: FunctorOf (Op k :**: k) v t => t -> Obj v (End v t)
  endCounit :: FunctorOf (Op k :**: k) v t => t -> Obj k a -> v (End v t) (t :% (a, a))
  endFactorizer :: FunctorOf (Op k :**: k) v t => t -> (forall a. Obj k a -> v x (t :% (a, a))) -> v x (End v t)

-- | Ends as Hom-weighted limits
instance HasEnds k => HasWLimits k (Hom k) where
  type WeightedLimit k (Hom k) d = End k d
  limitObj Hom d = end d
  limit Hom d (Op a :**: _) ab = d % (Op a :**: ab) . endCounit d a
  limitFactorizer Hom d _ f = endFactorizer d (\a -> f (Op a :**: a) a)

data EndFunctor (k :: Type -> Type -> Type) (v :: Type -> Type -> Type) = EndFunctor
instance (HasEnds v, Category k) => Functor (EndFunctor k v) where
  type Dom (EndFunctor k v) = Nat (Op k :**: k) v
  type Cod (EndFunctor k v) = v
  type EndFunctor k v :% t = End v t

  EndFunctor % Nat f g n = endFactorizer g (\a -> n (Op a :**: a) . endCounit f a)

newtype HaskEnd t = HaskEnd { getHaskEnd :: forall k a. FunctorOf (Op k :**: k) (->) t => t -> Obj k a -> t :% (a, a) }
instance HasEnds (->) where
  type End (->) t = HaskEnd t
  end _ e = e
  endCounit t a (HaskEnd f) = f t a
  endFactorizer _ e x = HaskEnd (\_ a -> e a x)


-- | @w@-weighted colimits in the category @k@.
class (Functor w, Cod w ~ (->), Category k) => HasWColimits k w where
  type WeightedColimit k w d :: Type
  colimitObj :: (FunctorOf j k d, Op j ~ Dom w) => w -> d -> Obj k (WColimit w d)
  colimit :: (FunctorOf j k d, Op j ~ Dom w) => w -> d -> Obj (Dom w) a -> w :% a -> k (d :% a) (WColimit w d)
  colimitFactorizer :: (FunctorOf j k d, Op j ~ Dom w) => w -> d -> Obj k e -> (forall a. Obj (Dom w) a -> w :% a -> k (d :% a) e) -> k (WColimit w d) e

type WColimit w d = WeightedColimit (Cod d) w d

-- | Regular colimits as weigthed colimits, weighted by the constant functor to '()'.
instance L.HasColimits j k => HasWColimits k (Const (Op j) (->) ()) where
  type WeightedColimit k (Const (Op j) (->) ()) d = L.Colimit d
  colimitObj (Const _) d = L.coconeVertex (L.colimit (natId d))
  colimit (Const _) d (Op a) () = L.colimit (natId d) ! a
  colimitFactorizer (Const _) d e f = L.colimitFactorizer (Nat d (Const e) (\z -> f (Op z) ()))


class Category v => HasCoends v where
  type Coend (v :: Type -> Type -> Type) t :: Type
  coend :: FunctorOf (Op k :**: k) v t => t -> Obj v (Coend v t)
  coendCounit :: FunctorOf (Op k :**: k) v t => t -> Obj k a -> v (t :% (a, a)) (Coend v t)
  coendFactorizer :: FunctorOf (Op k :**: k) v t => t -> (forall a. Obj k a -> v (t :% (a, a)) x) -> v (Coend v t) x

data OpHom (k :: Type -> Type -> Type) = OpHom
-- | The Hom-functor but with opposite domain.
instance Category k => Functor (OpHom k) where
  type Dom (OpHom k) = Op (Op k :**: k)
  type Cod (OpHom k) = (->)
  type OpHom k :% (a1, a2) = k a2 a1
  OpHom % Op (Op f1 :**: f2) = \g -> f1 . g . f2

-- | Coends as OpHom-weighted colimits
instance HasCoends k => HasWColimits k (OpHom k) where
  type WeightedColimit k (OpHom k) d = Coend k d
  colimitObj OpHom d = coend d
  colimit OpHom d (Op (Op a :**: _)) ab = coendCounit d a . d % (Op a :**: ab)
  colimitFactorizer OpHom d _ f = coendFactorizer d (\a -> f (Op (Op a :**: a)) a)

data CoendFunctor (k :: Type -> Type -> Type) (v :: Type -> Type -> Type) = CoendFunctor
instance (HasCoends v, Category k) => Functor (CoendFunctor k v) where
  type Dom (CoendFunctor k v) = Nat (Op k :**: k) v
  type Cod (CoendFunctor k v) = v
  type CoendFunctor k v :% t = Coend v t

  CoendFunctor % Nat f g n = coendFactorizer f (\a -> coendCounit g a . n (Op a :**: a))

data HaskCoend t where
  HaskCoend :: FunctorOf (Op k :**: k) (->) t => t -> Obj k a -> t :% (a, a) -> HaskCoend t
instance HasCoends (->) where
  type Coend (->) t = HaskCoend t
  coend _ e = e
  coendCounit t a taa = HaskCoend t a taa
  coendFactorizer _ f (HaskCoend _ a taa) = f a taa
