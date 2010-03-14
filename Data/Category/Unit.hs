{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}
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

-- | The one object of /1/.
data UnitO = UnitO

-- | The arrows of Unit.
data family Unit a b :: *
data instance Unit UnitO UnitO = UnitId

instance Apply Unit UnitO UnitO where
  UnitId $$ UnitO = UnitO
  
instance CategoryO Unit UnitO where
  id = UnitId
instance CategoryA Unit UnitO UnitO UnitO where
  UnitId . UnitId = UnitId
