{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, EmptyDataDecls, FlexibleInstances #-}
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
  IdZ :: Omega Z Z
  GTZ :: Omega Z n -> Omega Z (S n)
  StS :: Omega a b -> Omega (S a) (S b)
  
instance Category Omega where
  
  data Obj Omega a where
    OZ :: Obj Omega Z
    OS :: Obj Omega n -> Obj Omega (S n)
  
  src IdZ     = OZ
  src (GTZ _) = OZ
  src (StS a) = OS (src a)
  
  tgt IdZ     = OZ
  tgt (GTZ a) = OS (tgt a)
  tgt (StS a) = OS (tgt a)
  
  id OZ             = IdZ
  id (OS n)         = StS (id n)
  
  a       . IdZ     = a
  (StS a) . (GTZ n) = GTZ (a . n)
  (StS a) . (StS b) = StS (a . b)
  _       . _       = error "Other combinations should not type check"


instance HasInitialObject Omega where
  
  type InitialObject Omega = Z
  
  initialObject     = OZ
  
  initialize OZ     = IdZ
  initialize (OS n) = GTZ $ initialize n


type instance BinaryProduct Omega Z     n = Z
type instance BinaryProduct Omega n     Z = Z
type instance BinaryProduct Omega (S a) (S b) = S (BinaryProduct Omega a b)

-- The product in omega is the minimum.
instance HasBinaryProducts Omega where 

  product OZ     _      = OZ
  product _      OZ     = OZ
  product (OS a) (OS b) = OS (product a b)
  
  proj1 OZ     OZ     = IdZ
  proj1 OZ     (OS n) = IdZ
  proj1 (OS n) OZ     = GTZ $ proj1 n OZ
  proj1 (OS a) (OS b) = StS $ proj1 a b
  proj2 OZ     OZ     = IdZ
  proj2 OZ     (OS n) = GTZ $ proj2 OZ n
  proj2 (OS n) OZ     = IdZ
  proj2 (OS a) (OS b) = StS $ proj2 a b
  
  IdZ   &&& _     = IdZ
  _     &&& IdZ   = IdZ
  GTZ a &&& GTZ b = GTZ (a &&& b)
  StS a &&& StS b = StS (a &&& b)
  _     &&& _      = error "Other combinations should not type check"


type instance BinaryCoproduct Omega Z     n     = n
type instance BinaryCoproduct Omega n     Z     = n
type instance BinaryCoproduct Omega (S a) (S b) = S (BinaryCoproduct Omega a b)

-- -- The coproduct in omega is the maximum.
instance HasBinaryCoproducts Omega where 
  
  coproduct OZ     n      = n
  coproduct n      OZ     = n
  coproduct (OS a) (OS b) = OS (coproduct a b)
  
  inj1 OZ     OZ     = IdZ
  inj1 OZ     (OS n) = GTZ $ inj1 OZ n
  inj1 (OS n) OZ     = StS $ inj1 n OZ
  inj1 (OS a) (OS b) = StS $ inj1 a b
  inj2 OZ     OZ     = IdZ
  inj2 OZ     (OS n) = StS $ inj2 OZ n
  inj2 (OS n) OZ     = GTZ $ inj2 n OZ
  inj2 (OS a) (OS b) = StS $ inj2 a b
  
  IdZ   ||| IdZ   = IdZ
  GTZ _ ||| a     = a
  a     ||| GTZ _ = a
  StS a ||| StS b = StS (a ||| b)
  _     ||| _      = error "Other combinations should not type check"
  
  
instance Show (Obj Omega a) where
  show OZ = "OZ"
  show (OS n) = "OS " ++ show n
