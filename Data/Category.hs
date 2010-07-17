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
  , Obj(..)
  
  -- * Opposite category
  , Op(..)
    
) where

import Prelude (($))
import qualified Prelude


-- | An instance of @Category (~>)@ declares the arrow @(~>)@ as a category.
class Category (~>) where
  data Obj (~>) :: * -> *

  src :: a ~> b -> Obj (~>) a
  tgt :: a ~> b -> Obj (~>) b

  id  :: Obj (~>) a -> a ~> a
  (.) :: b ~> c -> a ~> b -> a ~> c


-- | The category with Haskell types as objects and Haskell functions as arrows.
instance Category (->) where
  data Obj (->) a = HaskO
  
  src _ = HaskO
  tgt _ = HaskO
  
  id _  = Prelude.id  
  (.)   = (Prelude..)    


data Op :: (* -> * -> *) -> * -> * -> * where
  Op :: (a ~> b) -> Op (~>) b a

-- | @Op (~>)@ is opposite category of the category @(~>)@.
instance Category (~>) => Category (Op (~>)) where
  data Obj (Op (~>)) a = OpObj (Obj (~>) a)
  
  src (Op a)      = OpObj $ tgt a
  tgt (Op a)      = OpObj $ src a
  
  id (OpObj x)    = Op $ id x
  (Op a) . (Op b) = Op $ b . a
