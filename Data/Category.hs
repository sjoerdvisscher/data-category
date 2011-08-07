{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category (
  
  -- * Category
    Category(..)
  , Obj
  
  -- * Opposite category
  , Op(..)
    
) where

infixr 8 .


-- | Whenever objects are required at value level, they are represented by their identity arrows.
type Obj (~>) a = a ~> a

-- | An instance of @Category (~>)@ declares the arrow @(~>)@ as a category.
class Category (~>) where
  
  src :: a ~> b -> Obj (~>) a
  tgt :: a ~> b -> Obj (~>) b

  (.) :: b ~> c -> a ~> b -> a ~> c


-- | The category with Haskell types as objects and Haskell functions as arrows.
instance Category (->) where
  
  src _ = \x -> x
  tgt _ = \x -> x
  
  f . g = \x -> f (g x)


data Op (~>) a b = Op { unOp :: b ~> a }

-- | @Op (~>)@ is opposite category of the category @(~>)@.
instance Category (~>) => Category (Op (~>)) where
  
  src (Op a)      = Op (tgt a)
  tgt (Op a)      = Op (src a)
  
  (Op a) . (Op b) = Op (b . a)
