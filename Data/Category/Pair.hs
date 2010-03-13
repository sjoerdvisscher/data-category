{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes #-}
module Data.Category.Pair where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Functor

data family Pair a b :: *

data Fst = Fst deriving Show
data Snd = Snd deriving Show

data instance Pair Fst Fst = IdFst
data instance Pair Snd Snd = IdSnd

instance Apply Pair Fst Fst where
  IdFst $$ Fst = Fst
instance Apply Pair Snd Snd where
  IdSnd $$ Snd = Snd
  
instance CategoryO Pair Fst where
  id = IdFst
instance CategoryO Pair Snd where
  id = IdSnd

instance CategoryA Pair Fst Fst Fst where
  IdFst . IdFst = IdFst
instance CategoryA Pair Snd Snd Snd where
  IdSnd . IdSnd = IdSnd

data instance Funct Pair d (FunctO Pair d f) (FunctO Pair d g) = 
  Component f g Fst :***: Component f g Snd
instance (CategoryO (Cod f) (F f Fst), CategoryO (Cod f) (F f Snd)) => CategoryO (Funct Pair d) (FunctO Pair d f) where
  id = id :***: id
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag Pair (~>)) a b where
  Diag % f = f :***: f


data PairF ((~>) :: * -> * -> *) x y a = PairF
type instance Dom (PairF (~>) x y) = Pair
type instance Cod (PairF (~>) x y) = (~>)
type instance F (PairF (~>) x y) Fst = x
type instance F (PairF (~>) x y) Snd = y
instance (CategoryO (~>) x) => FunctorA (PairF (~>) x y) Fst Fst where
  PairF % IdFst = id
instance (CategoryO (~>) y) => FunctorA (PairF (~>) x y) Snd Snd where
  PairF % IdSnd = id
