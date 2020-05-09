{-# LANGUAGE TypeOperators, RankNTypes, GADTs, TypeFamilies, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.End
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.End where

import Data.Category
import Data.Category.Functor
import Data.Category.Product
import Data.Category.NaturalTransformation


class Category v => HasEnds v where
  type End (v :: * -> * -> *) t :: *
  end :: FunctorOf (Op k :**: k) v t => t -> Obj v (End v t)
  endCounit :: FunctorOf (Op k :**: k) v t => t -> Obj k a -> v (End v t) (t :% (a, a))
  endFactorizer :: FunctorOf (Op k :**: k) v t => t -> (forall a. Obj k a -> v x (t :% (a, a))) -> v x (End v t)


class Category v => HasCoends v where
  type Coend (v :: * -> * -> *) t :: *
  coend :: FunctorOf (Op k :**: k) v t => t -> Obj v (Coend v t)
  coendCounit :: FunctorOf (Op k :**: k) v t => t -> Obj k a -> v (t :% (a, a)) (Coend v t)
  coendFactorizer :: FunctorOf (Op k :**: k) v t => t -> (forall a. Obj k a -> v (t :% (a, a)) x) -> v (Coend v t) x


data EndFunctor (k :: * -> * -> *) (v :: * -> * -> *) = EndFunctor
instance (HasEnds v, Category k) => Functor (EndFunctor k v) where
  type Dom (EndFunctor k v) = Nat (Op k :**: k) v
  type Cod (EndFunctor k v) = v
  type EndFunctor k v :% t = End v t

  EndFunctor % Nat f g n = endFactorizer g (\a -> n (Op a :**: a) . endCounit f a)


data CoendFunctor (k :: * -> * -> *) (v :: * -> * -> *) = CoendFunctor
instance (HasCoends v, Category k) => Functor (CoendFunctor k v) where
  type Dom (CoendFunctor k v) = Nat (Op k :**: k) v
  type Cod (CoendFunctor k v) = v
  type CoendFunctor k v :% t = Coend v t

  CoendFunctor % Nat f g n = coendFactorizer f (\a -> coendCounit g a . n (Op a :**: a))


newtype HaskEnd t = HaskEnd { getHaskEnd :: forall k a. FunctorOf (Op k :**: k) (->) t => t -> Obj k a -> t :% (a, a) }
instance HasEnds (->) where
  type End (->) t = HaskEnd t
  end _ e = e
  endCounit t a (HaskEnd f) = f t a
  endFactorizer _ e x = HaskEnd (\_ a -> e a x)

data HaskCoend t where
  HaskCoend :: FunctorOf (Op k :**: k) (->) t => t -> Obj k a -> t :% (a, a) -> HaskCoend t
instance HasCoends (->) where
  type Coend (->) t = HaskCoend t
  coend _ e = e
  coendCounit t a taa = HaskCoend t a taa
  coendFactorizer _ f (HaskCoend _ a taa) = f a taa
