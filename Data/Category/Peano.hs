{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Peano
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-- 
-- A Peano category as in "When is one thing equal to some other thing?"
-- Barry Mazur, 2007
-----------------------------------------------------------------------------
module Data.Category.Peano where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Void

data PeanoO (~>) x = PeanoO (TerminalObject (~>) ~> x) (x ~> x)

data family Peano ((~>) :: * -> * -> *) a b :: *
newtype instance Peano (~>) (PeanoO (~>) a) (PeanoO (~>) b) = PeanoA { unPeanoA :: a ~> b }

newtype instance Nat (Peano (~>)) d f g =
  PeanoNat { unPeanoNat :: forall x. CategoryO (~>) x => Obj (PeanoO (~>) x) -> Component f g (PeanoO (~>) x) }

type family PeanoCarrier p :: *
type instance PeanoCarrier (PeanoO (~>) x) = x

getPeanoCarrier :: PeanoO (~>) x -> x
getPeanoCarrier _ = obj :: x

instance Category (~>) => Category (Peano (~>)) where
  idNat = PeanoNat $ \x -> PeanoA (idNat ! getPeanoCarrier x)
instance CategoryO (~>) x => CategoryO (Peano (~>)) (PeanoO (~>) x) where
  (!) = unPeanoNat
instance CategoryA (~>) a b c => CategoryA (Peano (~>)) (PeanoO (~>) a) (PeanoO (~>) b) (PeanoO (~>) c) where
  (PeanoA f) . (PeanoA g) = PeanoA (f . g)