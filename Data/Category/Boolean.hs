{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, GADTs, EmptyDataDecls, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Boolean
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- /2/, or the Boolean category. 
-- It contains 2 objects, one for true and one for false.
-- It contains 3 arrows, 2 identity arrows and one from false to true.
-----------------------------------------------------------------------------
module Data.Category.Boolean where

import Prelude hiding ((.), id, Functor)

import Data.Category
import Data.Category.Limit


data Fls
data Tru
  
data Boolean a b where
  Fls :: Boolean Fls Fls
  F2T :: Boolean Fls Tru
  Tru :: Boolean Tru Tru

-- | @Boolean@ is the category with true and false as objects, and an arrow from false to true.
instance Category Boolean where
  
  src Fls   = Fls
  src F2T   = Fls
  src Tru   = Tru
  
  tgt Fls   = Fls
  tgt F2T   = Tru
  tgt Tru   = Tru
  
  Fls . Fls = Fls
  F2T . Fls = F2T
  Tru . F2T = F2T
  Tru . Tru = Tru
  _      . _      = error "Other combinations should not type check"


-- | False is the initial object in the Boolean category.
instance HasInitialObject Boolean where
  type InitialObject Boolean = Fls
  initialObject = Fls
  initialize Fls = Fls
  initialize Tru = F2T
  initialize _   = error "Other values should not type check"
  
-- | True is the terminal object in the Boolean category.
instance HasTerminalObject Boolean where
  type TerminalObject Boolean = Tru
  terminalObject = Tru
  terminate Fls = F2T
  terminate Tru = Tru
  terminate _   = error "Other values should not type check"


type instance BinaryProduct Boolean Fls Fls = Fls
type instance BinaryProduct Boolean Fls Tru = Fls
type instance BinaryProduct Boolean Tru Fls = Fls
type instance BinaryProduct Boolean Tru Tru = Tru

instance HasBinaryProducts Boolean where 
  
  proj1 Fls Fls = Fls
  proj1 Fls Tru = Fls
  proj1 Tru Fls = F2T
  proj1 Tru Tru = Tru
  proj1 _   _   = error "Other combinations should not type check"
  proj2 Fls Fls = Fls
  proj2 Fls Tru = F2T
  proj2 Tru Fls = Fls
  proj2 Tru Tru = Tru
  proj2 _   _   = error "Other combinations should not type check"
    
  Fls &&& Fls = Fls
  Fls &&& F2T = Fls
  F2T &&& Fls = Fls
  F2T &&& F2T = F2T
  Tru &&& Tru = Tru
  _   &&& _   = error "Other combinations should not type check"


type instance BinaryCoproduct Boolean Fls Fls = Fls
type instance BinaryCoproduct Boolean Fls Tru = Tru
type instance BinaryCoproduct Boolean Tru Fls = Tru
type instance BinaryCoproduct Boolean Tru Tru = Tru

instance HasBinaryCoproducts Boolean where 
  
  inj1 Fls Fls = Fls
  inj1 Fls Tru = F2T
  inj1 Tru Fls = Tru
  inj1 Tru Tru = Tru
  inj1 _   _   = error "Other combinations should not type check"
  inj2 Fls Fls = Fls
  inj2 Fls Tru = Tru
  inj2 Tru Fls = F2T
  inj2 Tru Tru = Tru
  inj2 _   _   = error "Other combinations should not type check"
    
  Fls ||| Fls = Fls
  F2T ||| F2T = F2T
  F2T ||| Tru = Tru
  Tru ||| F2T = Tru
  Tru ||| Tru = Tru
  _   ||| _   = error "Other combinations should not type check"
