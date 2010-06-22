{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances #-}
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
-- A Peano category as in @When is one thing equal to some other thing?@
-- Barry Mazur, 2007
-----------------------------------------------------------------------------
module Data.Category.Peano where

import Prelude(($))

import Data.Category
import Data.Category.Limit


data Peano :: (* -> * -> *) -> * -> * -> * where
  PeanoA :: Obj (Peano (~>)) a -> Obj (Peano (~>)) b -> (a ~> b) -> Peano (~>) a b

instance Category (~>) => Category (Peano (~>)) where
  
  data Obj (Peano (~>)) a where
    PeanoO :: Obj (~>) x -> x -> (x ~> x) -> Obj (Peano (~>)) x
    
  src (PeanoA s _ _) = s
  tgt (PeanoA _ t _) = t
  
  id p@(PeanoO x _ _)             = PeanoA p p $ id x
  (PeanoA _ t f) . (PeanoA s _ g) = PeanoA s t $ f . g
  
  
-- | The natural numbers are the initial object for the 'Peano' category.
data NatNum = Z | S NatNum

-- | Primitive recursion is the factorizer from the natural numbers.
primRec :: t -> (t -> t) -> NatNum -> t
primRec z _ Z     = z
primRec z s (S n) = s (primRec z s n)
  
instance HasInitialObject (Peano (->)) where
  
  type InitialObject (Peano (->)) = NatNum
  
  initialObject = PeanoO HaskO Z S
  
  initialize o@(PeanoO HaskO z s) = PeanoA initialObject o $ primRec z s