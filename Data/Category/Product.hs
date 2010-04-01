{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
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

import Prelude hiding ((.), id)

import Data.Category

data family ((c1 :: * -> * -> *) :*: (c2 :: * -> * -> *)) a b :: *
data instance (c1 :*: c2) (a1, a2) (b1, b2) = (c1 a1 b1) :**: (c2 a2 b2)

data instance Nat (c1 :*: c2) d f g = 
  ProductNat { unProductNat :: forall a1 a2. (CategoryO c1 a1, CategoryO c2 a2) => Obj (a1, a2) -> Component f g (a1, a2) }

instance (Category c1, Category c2) => Category (c1 :*: c2) where
  idNat = ProductNat $ \(a1, a2) -> (idNat ! a1) :**: (idNat ! a2)
instance (CategoryO c1 a1, CategoryO c2 a2) => CategoryO (c1 :*: c2) (a1, a2) where
  (!) = unProductNat
  
data ProdF f1 f2 = ProdF
type instance Dom (ProdF f1 f2) = Dom f1 :*: Dom f2
type instance Cod (ProdF f1 f2) = Cod f1 :*: Cod f2
type instance F (ProdF f1 f2) (a1, a2) = (F f1 a1, F f2 a2)

data DiagProd ((~>) :: * -> * -> *) = DiagProd
type instance Dom (DiagProd (~>)) = (~>)
type instance Cod (DiagProd (~>)) = (~>) :*: (~>)
type instance F (DiagProd (~>)) a = (a, a)