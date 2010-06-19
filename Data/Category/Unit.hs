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
  UnitId :: Unit UnitO UnitO

instance Category Unit where
  
  data Obj Unit a where
    UnitO :: Obj Unit UnitO
  
  src UnitId = UnitO
  tgt UnitId = UnitO
  
  id UnitO        = UnitId
  UnitId . UnitId = UnitId
