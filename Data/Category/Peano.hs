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

data PeanoO (~>) x = PeanoO x (x ~> x)

data family Peano ((~>) :: * -> * -> *) a b :: *
newtype instance Peano (~>) (PeanoO (~>) a) (PeanoO (~>) b) = PeanoA (a ~> b)

newtype instance Nat (Peano (~>)) d f g =
  PeanoNat { unPeanoNat :: forall x. PeanoO (~>) x -> Component f g (PeanoO (~>) x) }

instance CategoryO (~>) x => CategoryO (Peano (~>)) (PeanoO (~>) x) where
  id = PeanoA id
  (!) = unPeanoNat
instance CategoryA (~>) a b c => CategoryA (Peano (~>)) (PeanoO (~>) a) (PeanoO (~>) b) (PeanoO (~>) c) where
  (PeanoA f) . (PeanoA g) = PeanoA (f . g)
  
instance VoidColimit (Peano (->)) where
  type InitialObject (Peano (->)) = PeanoO (->) Integer
  voidColimit = InitialUniversal VoidNat
    (PeanoNat $ \(PeanoO z s) VoidNat -> PeanoA $ let { f 0 = z; f (n + 1) = s (f n) } in f)