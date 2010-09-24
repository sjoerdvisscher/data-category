{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category
-- Copyright   :  (c) Sjoerd Visscher 2010
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

import Prelude (($))
import qualified Prelude

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
  
  src _ = Prelude.id
  tgt _ = Prelude.id
  
  (.)   = (Prelude..)    


data Op :: (* -> * -> *) -> * -> * -> * where
  Op :: (a ~> b) -> Op (~>) b a

-- | @Op (~>)@ is opposite category of the category @(~>)@.
instance Category (~>) => Category (Op (~>)) where
  
  src (Op a)      = Op $ tgt a
  tgt (Op a)      = Op $ src a
  
  (Op a) . (Op b) = Op $ b . a
