{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Product
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Product where

import Prelude ()

import Data.Category
import Data.Category.Functor


data (:**:) :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  (:**:) :: c1 a1 b1 -> c2 a2 b2 -> (:**:) c1 c2 (a1, a2) (b1, b2)

-- | The product category of category @c1@ and @c2@.
instance (Category c1, Category c2) => Category (c1 :**: c2) where
  
  src (a1 :**: a2)            = src a1 :**: src a2
  tgt (a1 :**: a2)            = tgt a1 :**: tgt a2
  
  (a1 :**: a2) . (b1 :**: b2) = (a1 . b1) :**: (a2 . b2)


  
  
    
data Proj1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Proj1
type instance Dom (Proj1 c1 c2) = c1 :**: c2
type instance Cod (Proj1 c1 c2) = c1
type instance Proj1 c1 c2 :% (a1, a2) = a1
instance (Category c1, Category c2) => Functor (Proj1 c1 c2) where 
  Proj1 % (f1 :**: _) = f1

data Proj2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Proj2
type instance Dom (Proj2 c1 c2) = c1 :**: c2
type instance Cod (Proj2 c1 c2) = c2
type instance Proj2 c1 c2 :% (a1, a2) = a2
instance (Category c1, Category c2) => Functor (Proj2 c1 c2) where 
  Proj2 % (_ :**: f2) = f2

data f1 :***: f2 = f1 :***: f2
type instance Dom (f1 :***: f2) = Dom f1 :**: Dom f2
type instance Cod (f1 :***: f2) = Cod f1 :**: Cod f2
type instance (f1 :***: f2) :% (a1, a2) = (f1 :% a1, f2 :% a2)
instance (Functor f1, Functor f2) => Functor (f1 :***: f2) where 
  (g1 :***: g2) % (f1 :**: f2) = (g1 % f1) :**: (g2 % f2)
  
data DiagProd ((~>) :: * -> * -> *) = DiagProd
type instance Dom (DiagProd (~>)) = (~>)
type instance Cod (DiagProd (~>)) = (~>) :**: (~>)
type instance DiagProd (~>) :% a = (a, a)
instance Category (~>) => Functor (DiagProd (~>)) where 
  DiagProd % f = f :**: f

data Tuple1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) a = Tuple1 (Obj c1 a)
type instance Dom (Tuple1 c1 c2 a1) = c2
type instance Cod (Tuple1 c1 c2 a1) = c1 :**: c2
type instance Tuple1 c1 c2 a1 :% a2 = (a1, a2)
instance (Category c1, Category c2) => Functor (Tuple1 c1 c2 a1) where
  Tuple1 a % f = a :**: f

data Tuple2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) a = Tuple2 (Obj c2 a)
type instance Dom (Tuple2 c1 c2 a2) = c1
type instance Cod (Tuple2 c1 c2 a2) = c1 :**: c2
type instance Tuple2 c1 c2 a2 :% a1 = (a1, a2)
instance (Category c1, Category c2) => Functor (Tuple2 c1 c2 a2) where
  Tuple2 a % f = f :**: a

