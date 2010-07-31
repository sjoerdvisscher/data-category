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
  
  proj OZ     OZ     = (IdZ, IdZ)
  proj OZ     (OS n) = (IdZ, GTZ . snd $ proj OZ n)
  proj (OS n) OZ     = (GTZ . fst $ proj n OZ, IdZ)
  proj (OS a) (OS b) = (StS proj1, StS proj2) where (proj1, proj2) = proj a b
  
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
  
  inj OZ OZ = (IdZ, IdZ)
  inj OZ (OS n) = (GTZ inj1, StS inj2) where (inj1, inj2) = inj OZ n
  inj (OS n) OZ = (StS inj1, GTZ inj2) where (inj1, inj2) = inj n OZ
  inj (OS a) (OS b) = (StS inj1, StS inj2) where (inj1, inj2) = inj a b
  
  IdZ   ||| IdZ   = IdZ
  GTZ _ ||| a     = a
  a     ||| GTZ _ = a
  StS a ||| StS b = StS (a ||| b)
  _     ||| _      = error "Other combinations should not type check"
  
  
instance Show (Obj Omega a) where
  show OZ = "OZ"
  show (OS n) = "OS " ++ show n
