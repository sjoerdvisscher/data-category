{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, FlexibleContexts, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Product
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Product where

import Data.Category


data (:**:) :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  (:**:) :: c1 a1 b1 -> c2 a2 b2 -> (:**:) c1 c2 (a1, a2) (b1, b2)

-- | The product category of categories @c1@ and @c2@.
instance (Category c1, Category c2) => Category (c1 :**: c2) where
  
  src (a1 :**: a2)            = src a1 :**: src a2
  tgt (a1 :**: a2)            = tgt a1 :**: tgt a2
  
  (a1 :**: a2) . (b1 :**: b2) = (a1 . b1) :**: (a2 . b2)