{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
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
  (:***:) { fstComp :: Component f g Fst, sndComp :: Component f g Snd }
instance (CategoryO (Cod f) (F f Fst), CategoryO (Cod f) (F f Snd)) => CategoryO (Funct Pair d) (FunctO Pair d f) where
  id = id :***: id
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag Pair (~>)) a b where
  Diag % f = f :***: f


data PairF ((~>) :: * -> * -> *) x y = PairF
type instance Dom (PairF (~>) x y) = Pair
type instance Cod (PairF (~>) x y) = (~>)
type instance F (PairF (~>) x y) Fst = x
type instance F (PairF (~>) x y) Snd = y
instance (CategoryO (~>) x) => FunctorA (PairF (~>) x y) Fst Fst where
  PairF % IdFst = id
instance (CategoryO (~>) y) => FunctorA (PairF (~>) x y) Snd Snd where
  PairF % IdSnd = id

class (CategoryO (~>) x, CategoryO (~>) y) => PairLimit (~>) x y where
  type Product x y :: *
  pairLimit :: Limit (PairF (~>) x y) (Product x y)
  proj1 :: Product x y ~> x
  proj2 :: Product x y ~> y
  proj1 = p where TerminalUniversal (p :***: _) _ = pairLimit :: Limit (PairF (~>) x y) (Product x y)
  proj2 = p where TerminalUniversal (_ :***: p) _ = pairLimit :: Limit (PairF (~>) x y) (Product x y)
class (CategoryO (~>) x, CategoryO (~>) y) => PairColimit (~>) x y where
  type Coproduct x y :: *
  pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  inj1 :: x ~> Coproduct x y
  inj2 :: y ~> Coproduct x y
  inj1 = i where InitialUniversal (i :***: _) _ = pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  inj2 = i where InitialUniversal (_ :***: i) _ = pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  