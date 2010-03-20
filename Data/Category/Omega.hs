{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Omega
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Omega, the category 0 -> 1 -> 2 -> 3 -> ... 
-- The objects are the natural numbers, and there's an arrow from a to b iff a <= b.
-----------------------------------------------------------------------------
module Data.Category.Omega where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair


-- | The object Z represents zero.
data Z = Z deriving Show
-- | The object S n represents the successor of n.
newtype S n = S n deriving Show

instance CategoryO Omega Z where
  id = IdZ
  OmegaNat z _ ! Z = z  
instance (CategoryO Omega n) => CategoryO Omega (S n) where
  id = StepS id
  on@(OmegaNat _ s) ! (S n) = s n (on ! n)

-- | The arrows of omega, there's an arrow from a to b iff a <= b.
data family Omega a b :: *
data instance Omega Z Z = IdZ
newtype instance Omega Z (S n) = GTZ (Omega Z n)
newtype instance Omega (S a) (S b) = StepS (Omega a b)

instance (CategoryO Omega n) => CategoryA Omega Z Z n where
  a . IdZ = a
instance (CategoryA Omega Z n p) => CategoryA Omega Z (S n) (S p) where
  (StepS a) . (GTZ n) = GTZ (a . n)
instance (CategoryA Omega n p q) => CategoryA Omega (S n) (S p) (S q) where
  (StepS a) . (StepS b) = StepS (a . b)

instance Apply Omega Z Z where
  IdZ $$ Z = Z
instance Apply Omega Z n => Apply Omega Z (S n) where
  GTZ d $$ Z = S (d $$ Z)
instance Apply Omega a b => Apply Omega (S a) (S b) where
  StepS d $$ S a = S (d $$ a)

data instance Nat Omega d f g = 
  OmegaNat (Component f g Z) (forall n. Obj n -> Component f g n -> Component f g (S n))


data OmegaF ((~>) :: * -> * -> *) z f = OmegaF
type instance Dom (OmegaF (~>) z f) = Omega
type instance Cod (OmegaF (~>) z f) = (~>)
type instance F (OmegaF (~>) z f) Z = z
type instance F (OmegaF (~>) z f) (S n) = F f (F (OmegaF (~>) z f) n)
instance CategoryO (~>) z => FunctorA (OmegaF (~>) z f) Z Z where
  OmegaF % IdZ = id

class CategoryO (~>) z => OmegaLimit (~>) z f where
  type OmegaL (~>) z f :: *
  omegaLimit :: Limit (OmegaF (~>) z f) (OmegaL (~>) z f)
class CategoryO (~>) z => OmegaColimit (~>) z f where
  type OmegaC (~>) z f :: *
  omegaColimit :: Colimit (OmegaF (~>) z f) (OmegaC (~>) z f)
  

instance VoidColimit Omega where
  type InitialObject Omega = Z
  voidColimit = InitialUniversal VoidNat (OmegaNat (\VoidNat -> IdZ) (\_ cpt VoidNat -> GTZ (cpt VoidNat)))

-- The product in omega is the minimum.
instance PairLimit Omega Z Z where 
  type Product Z Z = Z
  pairLimit = TerminalUniversal (IdZ :***: IdZ) undefined
instance (PairLimit Omega Z n, Product Z n ~ Z) => PairLimit Omega Z (S n) where 
  type Product Z (S n) = Z
  pairLimit = TerminalUniversal (IdZ :***: GTZ p) undefined where
    TerminalUniversal (_ :***: p) _ = pairLimit :: Limit (PairF Omega Z n) (Product Z n)
instance (PairLimit Omega n Z, Product n Z ~ Z) => PairLimit Omega (S n) Z where 
  type Product (S n) Z = Z
  pairLimit = TerminalUniversal (GTZ p :***: IdZ) undefined where
    TerminalUniversal (p :***: _) _ = pairLimit :: Limit (PairF Omega n Z) (Product n Z)
instance (PairLimit Omega a b) => PairLimit Omega (S a) (S b) where 
  type Product (S a) (S b) = S (Product a b)
  pairLimit = TerminalUniversal (StepS p1 :***: StepS p2) undefined where
    TerminalUniversal (p1 :***: p2) _ = pairLimit :: Limit (PairF Omega a b) (Product a b)

-- The coproduct in omega is the maximum.
instance PairColimit Omega Z Z where 
  type Coproduct Z Z = Z
  pairColimit = InitialUniversal (IdZ :***: IdZ) undefined
instance (PairColimit Omega Z n, Coproduct Z n ~ n) => PairColimit Omega Z (S n) where 
  type Coproduct Z (S n) = S n
  pairColimit = InitialUniversal (GTZ p1 :***: StepS p2) undefined where
    InitialUniversal (p1 :***: p2) _ = pairColimit :: Colimit (PairF Omega Z n) (Coproduct Z n)
instance (PairColimit Omega n Z, Coproduct n Z ~ n) => PairColimit Omega (S n) Z where 
  type Coproduct (S n) Z = S n
  pairColimit = InitialUniversal (StepS p1 :***: GTZ p2) undefined where
    InitialUniversal (p1 :***: p2) _ = pairColimit :: Colimit (PairF Omega n Z) (Coproduct n Z)
instance (PairColimit Omega a b) => PairColimit Omega (S a) (S b) where 
  type Coproduct (S a) (S b) = S (Coproduct a b)
  pairColimit = InitialUniversal (StepS p1 :***: StepS p2) undefined where
    InitialUniversal (p1 :***: p2) _ = pairColimit :: Colimit (PairF Omega a b) (Coproduct a b)
