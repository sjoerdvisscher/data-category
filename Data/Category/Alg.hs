{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Alg
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Alg(F), the category of F-algebras and F-homomorphisms.
-----------------------------------------------------------------------------
module Data.Category.Alg where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Void

-- | Objects of Alg(F) are F-algebras.
newtype AlgO f a = AlgO (Dom f (F f a) a)

-- | Arrows of Alg(F) are F-homomorphisms.
data family Alg f a b :: *
data instance Alg f (AlgO f a) (AlgO f b) = AlgA (Dom f a b)

newtype instance Nat (Alg f) d g h = 
  AlgNat { unAlgNat :: forall a. Obj (AlgO f a) -> Component g h (AlgO f a) }

instance (Dom f ~ (~>), Cod f ~ (~>), CategoryO (~>) a) => CategoryO (Alg f) (AlgO f a) where
  id = AlgA id
  (!) = unAlgNat
instance (Dom f ~ (~>), Cod f ~ (~>), CategoryA (~>) a b c) => CategoryA (Alg f) (AlgO f a) (AlgO f b) (AlgO f c) where
  AlgA f . AlgA g = AlgA (f . g)

-- | Showing that @[a]@ is the initial object in @Alg (LiftF a)@.
data ListF a = ListF
type instance Dom (ListF a) = (->)
type instance Cod (ListF a) = (->)
type instance F (ListF a) r = Either () (a, r)

initializeListF :: AlgO (ListF a) b -> Alg (ListF a) (AlgO (ListF a) [a]) (AlgO (ListF a) b)
initializeListF (AlgO f) = AlgA $ foldr (\x xs -> f (Right (x, xs))) (f (Left ()))

instance VoidColimit (Alg (ListF a)) where
  type InitialObject (Alg (ListF a)) = AlgO (ListF a) [a]
  voidColimit = InitialUniversal VoidNat (AlgNat $ \f VoidNat -> initializeListF f)

