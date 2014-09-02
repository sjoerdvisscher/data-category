{-# LANGUAGE TypeFamilies, GADTs, RankNTypes, TypeOperators, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Cube
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The cube category.
-----------------------------------------------------------------------------
module Data.Category.Cube where

import Data.Category
import Data.Category.Product
import Data.Category.Functor
import Data.Category.Monoidal
import Data.Category.Limit


data Z
data S n


data Sign = M | P

data Cube :: * -> * -> * where
  Z :: Cube Z Z
  S :: Cube x y -> Cube (S x) (S y)
  Y :: Sign -> Cube x y -> Cube x (S y) -- face maps
  X :: Cube x y -> Cube (S x) y -- degeneracy map


instance Category Cube where
  src Z = Z
  src (S c) = S (src c)
  src (Y _ c) = src c
  src (X c) = S (src c)

  tgt Z = Z
  tgt (S c) = S (tgt c)
  tgt (Y _ c) = S (tgt c)
  tgt (X c) = tgt c

  Z . c = c
  c . Z = c
  S c . S d = S (c . d)
  S c . Y s d = Y s (c . d)
  Y s c . d = Y s (c . d)
  X c . S d = X (c . d)
  X c . Y _ d = c . d
  c . X d = X (c . d)


instance HasTerminalObject Cube where
  type TerminalObject Cube = Z

  terminalObject = Z

  terminate Z = Z
  terminate (S f) = X (terminate f)


data Sign0 = SM | S0 | SP

data ACube :: * -> * where
  Nil :: ACube Z
  Cons :: Sign0 -> ACube n -> ACube (S n)

data Forget = Forget
-- | Turn @Cube x y@ arrows into @ACube x -> ACube y@ functions.
instance Functor Forget where
  type Dom Forget = Cube
  type Cod Forget = (->)
  type Forget :% n = ACube n
  Forget % Z     = \x -> x
  Forget % S f   = \(Cons s x) -> Cons s ((Forget % f) x)
  Forget % Y M f = \x -> Cons SM ((Forget % f) x)
  Forget % Y P f = \x -> Cons SP ((Forget % f) x)
  Forget % X f   = \(Cons _ x) -> (Forget % f) x


data Add = Add
-- | Ordinal addition is a bifuntor, it concattenates the maps as it were.
instance Functor Add where
  type Dom Add = Cube :**: Cube
  type Cod Add = Cube
  type Add :% (Z  , n) = n
  type Add :% (S m, n) = S (Add :% (m, n))
  Add % (Z     :**: g) = g
  Add % (S f   :**: g) = S   (Add % (f :**: g))
  Add % (Y s f :**: g) = Y s (Add % (f :**: g))
  Add % (X f   :**: g) = X   (Add % (f :**: g))


instance TensorProduct Add where
  type Unit Add = Z
  unitObject Add = Z

  leftUnitor     Add    a  = a
  leftUnitorInv  Add    a  = a
  rightUnitor    Add    Z  = Z
  rightUnitor    Add (S n) = S (rightUnitor Add n)
  rightUnitorInv Add    Z  = Z
  rightUnitorInv Add (S n) = S (rightUnitorInv Add n)
  associator     Add Z    Z  n = n
  associator     Add Z (S m) n = S (associator Add Z m n)
  associator     Add (S l) m n = S (associator Add l m n)
  associatorInv  Add Z    Z  n = n
  associatorInv  Add Z (S m) n = S (associatorInv Add Z m n)
  associatorInv  Add (S l) m n = S (associatorInv Add l m n)
