{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Peano
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


data PeanoO (~>) a where
  PeanoO :: (TerminalObject (~>) ~> x) -> (x ~> x) -> PeanoO (~>) x
    
data Peano :: (* -> * -> *) -> * -> * -> * where
  PeanoA :: PeanoO (~>) a -> PeanoO (~>) b -> (a ~> b) -> Peano (~>) a b

peanoId :: Category (~>) => PeanoO (~>) a -> Obj (Peano (~>)) a
peanoId o@(PeanoO z _) = PeanoA o o $ tgt z

peanoO :: Category (~>) => Obj (Peano (~>)) a -> PeanoO (~>) a
peanoO (PeanoA o _ _) = o

instance HasTerminalObject (~>) => Category (Peano (~>)) where
  
  src (PeanoA s _ _) = peanoId s
  tgt (PeanoA _ t _) = peanoId t
  
  (PeanoA _ t f) . (PeanoA s _ g) = PeanoA s t $ f . g
  
  
data NatNum = Z () | S NatNum

-- | Primitive recursion is the factorizer from the natural numbers.
primRec :: (() -> t) -> (t -> t) -> NatNum -> t
primRec z _ (Z ()) = z ()
primRec z s (S  n) = s (primRec z s n)
  
-- | The natural numbers are the initial object for the 'Peano' category.
instance HasInitialObject (Peano (->)) where
  
  type InitialObject (Peano (->)) = NatNum
  
  initialObject = peanoId $ PeanoO Z S
  
  initialize (peanoO -> o@(PeanoO z s)) = PeanoA (peanoO initialObject) o $ primRec z s
