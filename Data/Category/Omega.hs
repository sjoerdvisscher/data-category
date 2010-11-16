{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances #-}
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

import Prelude hiding ((.), id, Functor, product)

import Data.Category
import Data.Category.Limit


data Z
data S n

-- | The arrows of omega, there's an arrow from a to b iff a <= b.
data Omega :: * -> * -> * where
  Z   :: Omega Z Z
  Z2S :: Omega Z n -> Omega Z (S n)
  S   :: Omega a b -> Omega (S a) (S b)
  
instance Category Omega where
  
  src Z       = Z
  src (Z2S _) = Z
  src (S   a) = S (src a)
  
  tgt Z       = Z
  tgt (Z2S a) = S (tgt a)
  tgt (S   a) = S (tgt a)
  
  a     . Z       = a
  (S a) . (Z2S n) = Z2S (a . n)
  (S a) . (S   b) = S   (a . b)
  _       . _     = error "Other combinations should not type check"


instance HasInitialObject Omega where
  
  type InitialObject Omega = Z
  
  initialObject    = Z
  
  initialize Z     = Z
  initialize (S n) = Z2S $ initialize n
  initialize _     = error "Other combinations should not type check"



type instance BinaryProduct Omega Z     n = Z
type instance BinaryProduct Omega n     Z = Z
type instance BinaryProduct Omega (S a) (S b) = S (BinaryProduct Omega a b)

-- The product in omega is the minimum.
instance HasBinaryProducts Omega where 

  proj1 Z     Z     = Z
  proj1 Z     (S _) = Z
  proj1 (S n) Z     = Z2S $ proj1 n Z
  proj1 (S a) (S b) = S $ proj1 a b
  proj1 _     _     = error "Other combinations should not type check"

  proj2 Z     Z     = Z
  proj2 Z     (S n) = Z2S $ proj2 Z n
  proj2 (S _) Z     = Z
  proj2 (S a) (S b) = S $ proj2 a b
  proj2 _     _     = error "Other combinations should not type check"
  
  Z     &&& _     = Z
  _     &&& Z     = Z
  Z2S a &&& Z2S b = Z2S (a &&& b)
  S a   &&& S b   = S (a &&& b)
  _     &&& _     = error "Other combinations should not type check"


type instance BinaryCoproduct Omega Z     n     = n
type instance BinaryCoproduct Omega n     Z     = n
type instance BinaryCoproduct Omega (S a) (S b) = S (BinaryCoproduct Omega a b)

-- -- The coproduct in omega is the maximum.
instance HasBinaryCoproducts Omega where 
  
  inj1 Z     Z     = Z
  inj1 Z     (S n) = Z2S $ inj1 Z n
  inj1 (S n) Z     = S $ inj1 n Z
  inj1 (S a) (S b) = S $ inj1 a b
  inj1 _     _     = error "Other combinations should not type check"
  inj2 Z     Z     = Z
  inj2 Z     (S n) = S $ inj2 Z n
  inj2 (S n) Z     = Z2S $ inj2 n Z
  inj2 (S a) (S b) = S $ inj2 a b
  inj2 _     _     = error "Other combinations should not type check"
  
  Z     ||| Z     = Z
  Z2S _ ||| a     = a
  a     ||| Z2S _ = a
  S a   ||| S b   = S (a ||| b)
  _     ||| _     = error "Other combinations should not type check"
