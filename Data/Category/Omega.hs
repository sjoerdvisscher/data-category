{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes #-}
module Data.Category.Omega where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair


-- Natural numbers, the omega Category 0 -> 1 -> 2 -> 3 ...
data family Omega a b :: * 

-- Objects
data Z = Z deriving Show
newtype S n = S n deriving Show

-- Arrows, there's an arrow from a to b when a is less than or equal to b
data instance Omega Z Z = IdZ
newtype instance Omega Z (S n) = GTZ (Omega Z n)
newtype instance Omega (S a) (S b) = StepS (Omega a b)

instance Apply Omega Z Z where
  IdZ $$ Z = Z
instance Apply Omega Z n => Apply Omega Z (S n) where
  GTZ d $$ Z = S (d $$ Z)
instance Apply Omega a b => Apply Omega (S a) (S b) where
  StepS d $$ S a = S (d $$ a)

instance CategoryO Omega Z where
  id = IdZ
instance (CategoryO Omega n) => CategoryO Omega (S n) where
  id = StepS id

instance (CategoryO Omega n) => CategoryA Omega Z Z n where
  a . IdZ = a
instance (CategoryA Omega Z n p) => CategoryA Omega Z (S n) (S p) where
  (StepS a) . (GTZ n) = GTZ (a . n)
instance (CategoryA Omega n p q) => CategoryA Omega (S n) (S p) (S q) where
  (StepS a) . (StepS b) = StepS (a . b)


data instance Funct Omega d (FunctO Omega d f) (FunctO Omega d g) = 
  OmegaNat (Component f g Z) (forall n. CategoryO d (F f (S n)) => Component f g n -> Component f g (S n))
instance (Dom f ~ Omega, Cod f ~ d, CategoryO (Cod f) (F f Z)) => CategoryO (Funct Omega d) (FunctO Omega d f) where
  id = OmegaNat id (const id)


initObjInOmega :: Colimit (VoidF Omega) Z
initObjInOmega = InitialUniversal VoidNat $ OmegaNat (\VoidNat -> IdZ) (\cpt VoidNat -> GTZ (cpt VoidNat))

type family Min x y :: *
type instance Min Z Z = Z
type instance Min Z (S n) = Z
type instance Min (S n) Z = Z
type instance Min (S a) (S b) = Min a b

prodLimitInOmegaZZ :: Limit (PairF Omega Z Z) (Min Z Z)
prodLimitInOmegaZZ = TerminalUniversal (IdZ :***: IdZ) $ OmegaNat (\(f :***: s) -> f) (\cpt (f :***: s) -> f)
prodLimitInOmegaZS :: Limit (PairF Omega Z (S n)) (Min Z (S n))
prodLimitInOmegaZS = TerminalUniversal (IdZ :***: GTZ undefined) $ OmegaNat (\(f :***: s) -> f) (\cpt (f :***: s) -> f)
