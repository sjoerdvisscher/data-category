{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Data.Category.Monoid where

import Prelude hiding ((.), id)
import Data.Monoid

import Data.Category

-- |A monoid as a category with one object.
newtype MonoidCat m a b = MonoidCat m

instance Monoid m => CategoryO (MonoidCat m) m where
  id = MonoidCat mempty
  
instance Monoid m => CategoryA (MonoidCat m) m m m where
  MonoidCat a . MonoidCat b = MonoidCat $ a `mappend` b
  
instance Monoid m => Apply (MonoidCat m) m m where
  MonoidCat a $$ b = a `mappend` b