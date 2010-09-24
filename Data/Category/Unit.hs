{-# LANGUAGE TypeFamilies, GADTs, EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Unit
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- /1/, The singleton category with just one object with only its identity arrow.
-----------------------------------------------------------------------------
module Data.Category.Unit where

import Data.Category

data UnitO

-- | The arrows of Unit.
data Unit a b where
  Unit :: Unit UnitO UnitO

-- | The singeleton category with just one object with only its identity arrow.
instance Category Unit where
  
  src Unit = Unit
  tgt Unit = Unit
  
  Unit . Unit = Unit
