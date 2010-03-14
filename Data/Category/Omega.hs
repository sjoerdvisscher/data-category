{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
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
newtype S n = S { unS :: n } deriving Show

-- Arrows, there's an arrow from a to b when a is less than or equal to b
data instance Omega Z Z = IdZ
newtype instance Omega Z (S n) = GTZ { unGTZ :: Omega Z n }
newtype instance Omega (S a) (S b) = StepS { unStepS :: Omega a b }

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

instance VoidColimit Omega where
  type InitialObject Omega = Z
  voidColimit = InitialUniversal VoidNat (OmegaNat (\VoidNat -> IdZ) (\cpt VoidNat -> GTZ (cpt VoidNat)))

-- The product in omega is the minimum.
instance PairLimit Omega Z Z where 
  type Product Z Z = Z
  pairLimit = TerminalUniversal (IdZ :***: IdZ) (OmegaNat fstComp (\cpt -> sndComp))
instance (PairLimit Omega Z n, Product Z n ~ Z) => PairLimit Omega Z (S n) where 
  type Product Z (S n) = Z
  pairLimit = TerminalUniversal (IdZ :***: GTZ p) (OmegaNat fstComp (\cpt -> fstComp)) where
    TerminalUniversal (_ :***: p) _ = pairLimit :: Limit (PairF Omega Z n) (Product Z n)
instance (PairLimit Omega n Z, Product n Z ~ Z) => PairLimit Omega (S n) Z where 
  type Product (S n) Z = Z
  pairLimit = TerminalUniversal (GTZ p :***: IdZ) (OmegaNat sndComp (\cpt -> sndComp)) where
    TerminalUniversal (p :***: _) _ = pairLimit :: Limit (PairF Omega n Z) (Product n Z)
instance (PairLimit Omega a b) => PairLimit Omega (S a) (S b) where 
  type Product (S a) (S b) = S (Product a b)
  pairLimit = TerminalUniversal (StepS p1 :***: StepS p2) undefined where
    TerminalUniversal (p1 :***: p2) _ = pairLimit :: Limit (PairF Omega a b) (Product a b)

-- The coproduct in omega is the maximum.
instance PairColimit Omega Z Z where 
  type Coproduct Z Z = Z
  pairColimit = InitialUniversal (IdZ :***: IdZ) (OmegaNat fstComp (\cpt -> sndComp))
instance (PairColimit Omega Z n, Coproduct Z n ~ n) => PairColimit Omega Z (S n) where 
  type Coproduct Z (S n) = S n
  pairColimit = InitialUniversal (GTZ p1 :***: StepS p2) (OmegaNat sndComp (\cpt -> sndComp)) where
    InitialUniversal (p1 :***: p2) _ = pairColimit :: Colimit (PairF Omega Z n) (Coproduct Z n)
instance (PairColimit Omega n Z, Coproduct n Z ~ n) => PairColimit Omega (S n) Z where 
  type Coproduct (S n) Z = S n
  pairColimit = InitialUniversal (StepS p1 :***: GTZ p2) (OmegaNat fstComp (\cpt -> fstComp)) where
    InitialUniversal (p1 :***: p2) _ = pairColimit :: Colimit (PairF Omega n Z) (Coproduct n Z)
instance (PairColimit Omega a b) => PairColimit Omega (S a) (S b) where 
  type Coproduct (S a) (S b) = S (Coproduct a b)
  pairColimit = InitialUniversal (StepS p1 :***: StepS p2) undefined where
    InitialUniversal (p1 :***: p2) _ = pairColimit :: Colimit (PairF Omega a b) (Coproduct a b)
