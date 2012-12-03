{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Peano
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.NNO where

import Data.Category
import Data.Category.Functor
import Data.Category.Limit
import Data.Category.Unit
import Data.Category.Coproduct
import Data.Category.Fix


class HasTerminalObject k => HasNaturalNumberObject k where
  
  type NaturalNumberObject k :: *
  
  zero :: k (TerminalObject k) (NaturalNumberObject k)
  succ :: k (NaturalNumberObject k) (NaturalNumberObject k)
  
  primRec :: k (TerminalObject k) a -> k a a -> k (NaturalNumberObject k) a
  
  
data NatNum = Z | S NatNum

instance HasNaturalNumberObject (->) where
  
  type NaturalNumberObject (->) = NatNum
  
  zero = \() -> Z
  succ = S
  
  primRec z _  Z    = z ()
  primRec z s (S n) = s (primRec z s n)


type Nat = Fix ((:++:) Unit)

instance HasNaturalNumberObject Cat where
  
  type NaturalNumberObject Cat = CatW Nat
  
  zero = CatA (Const (Fix (I1 Unit)))
  succ = CatA (Wrap :.: Inj2)
  
  primRec (CatA z) (CatA s) = CatA (PrimRec z s)
  
data PrimRec z s = PrimRec z s
type instance Dom (PrimRec z s) = Nat
type instance Cod (PrimRec z s) = Cod z
type instance PrimRec z s :% I1 () = z :% ()
type instance PrimRec z s :% I2 n  = s :% PrimRec z s :% n
instance (Functor z, Functor s, Dom z ~ Unit, Cod z ~ Dom s, Dom s ~ Cod s) => Functor (PrimRec z s) where
  PrimRec z s % Fix (I1 Unit) = z % Unit
  PrimRec z s % Fix (I2 n) = s % PrimRec z s % n