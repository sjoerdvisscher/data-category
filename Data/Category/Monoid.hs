{-# LANGUAGE TypeFamilies, GADTs, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Monoid
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A monoid as a category with one object.
-----------------------------------------------------------------------------
module Data.Category.Monoid where

import Prelude hiding ((.), Functor)
import Data.Monoid

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction
import Data.Category.Monoidal as M

-- | The arrows are the values of the monoid.
data MonoidA m a b where
  MonoidA :: Monoid m => m -> MonoidA m m m

-- | A monoid as a category with one object.
instance Monoid m => Category (MonoidA m) where
  
  src (MonoidA _) = MonoidA mempty
  tgt (MonoidA _) = MonoidA mempty
  
  MonoidA a . MonoidA b = MonoidA $ a `mappend` b


data Mon :: * -> * -> * where
  MonoidMorphism :: (Monoid m1, Monoid m2) => (m1 -> m2) -> Mon m1 m2

unMonoidMorphism :: (Monoid m1, Monoid m2) => Mon m1 m2 -> m1 -> m2
unMonoidMorphism (MonoidMorphism f) = f

-- | The category of all monoids, with monoid morphisms as arrows.
instance Category Mon where
  
  src (MonoidMorphism _) = MonoidMorphism id
  tgt (MonoidMorphism _) = MonoidMorphism id
  
  MonoidMorphism f . MonoidMorphism g = MonoidMorphism $ f . g


data ForgetMonoid = ForgetMonoid
type instance Dom ForgetMonoid = Mon
type instance Cod ForgetMonoid = (->)
type instance ForgetMonoid :% a = a
instance Functor ForgetMonoid where
  ForgetMonoid % MonoidMorphism f = f
  
data FreeMonoid = FreeMonoid
type instance Dom FreeMonoid = (->)
type instance Cod FreeMonoid = Mon
type instance FreeMonoid :% a = [a]
instance Functor FreeMonoid where
  FreeMonoid % f = MonoidMorphism $ map f

freeMonoidAdj :: Adjunction Mon (->) FreeMonoid ForgetMonoid
freeMonoidAdj = mkAdjunction FreeMonoid ForgetMonoid (\_ -> (:[])) (\(MonoidMorphism _) -> MonoidMorphism mconcat)

foldMap :: Monoid m => (a -> m) -> [a] -> m
foldMap = unMonoidMorphism . rightAdjunct freeMonoidAdj (MonoidMorphism id)

listMonadReturn :: a -> [a]
listMonadReturn = M.unit (adjunctionMonad freeMonoidAdj) ! id

listMonadJoin :: [[a]] -> [a]
listMonadJoin = M.multiply (adjunctionMonad freeMonoidAdj) ! id

listComonadExtract :: Monoid m => [m] -> m
listComonadExtract = let MonoidMorphism f = M.counit (adjunctionComonad freeMonoidAdj) ! MonoidMorphism id in f

listComonadDuplicate :: Monoid m => [m] -> [[m]]
listComonadDuplicate = let MonoidMorphism f = M.comultiply (adjunctionComonad freeMonoidAdj) ! MonoidMorphism id in f
