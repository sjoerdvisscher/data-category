{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}
module Data.Category.Unit where

import Data.Category

-- "1", Singleton category
data family Unit a b :: *

data instance Unit () () = UnitId

instance Apply Unit () () where
  UnitId $$ () = ()
  
instance CategoryO Unit () where
  id = UnitId
instance CategoryA Unit () () () where
  UnitId . UnitId = UnitId
