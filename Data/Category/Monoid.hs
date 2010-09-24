{-# LANGUAGE TypeFamilies, GADTs, FlexibleInstances #-}
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
data MonoidA m a b where
  MonoidA :: Monoid m => m -> MonoidA m m m

instance Monoid m => Category (MonoidA m) where
  
  src (MonoidA _) = MonoidA mempty
  tgt (MonoidA _) = MonoidA mempty
  
  MonoidA a . MonoidA b = MonoidA $ a `mappend` b
