{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Monoid
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A monoid as a category with one object.
-----------------------------------------------------------------------------
module Data.Category.Monoid where

import Prelude hiding ((.), id)
import Data.Monoid

import Data.Category

-- | The arrows are the values of the monoid.
newtype MonoidA m a b = MonoidA m

newtype instance Nat (MonoidA m) d f g =
  MonoidNat (Component f g m)

instance Monoid m => CategoryO (MonoidA m) m where
  id = MonoidA mempty
  MonoidNat c ! _ = c  
instance Monoid m => CategoryA (MonoidA m) m m m where
  MonoidA a . MonoidA b = MonoidA $ a `mappend` b
instance Monoid m => Apply (MonoidA m) m m where
  MonoidA a $$ b = a `mappend` b