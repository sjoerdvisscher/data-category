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


data BF
data BT
  
data Boolean a b where
  IdFls  :: Boolean BF BF
  FlsTru :: Boolean BF BT
  IdTru  :: Boolean BT BT

instance Category Boolean where
  data Obj Boolean a where
    Fls :: Obj Boolean BF
    Tru :: Obj Boolean BT
  
  src IdFls  = Fls
  src FlsTru = Fls
  src IdTru  = Tru
  
  tgt IdFls  = Fls
  tgt FlsTru = Tru
  tgt IdTru  = Tru
  
  id Fls     = IdFls
  id Tru     = IdTru
  
  IdFls  . IdFls  = IdFls
  FlsTru . IdFls  = FlsTru
  IdTru  . FlsTru = FlsTru
  IdTru  . IdTru  = IdTru
  _      . _      = error "Other combinations should not type check"


instance HasInitialObject Boolean where
  type InitialObject Boolean = BF
  initialObject = Fls
  initialize Fls = IdFls
  initialize Tru = FlsTru
  
instance HasTerminalObject Boolean where
  type TerminalObject Boolean = BT
  terminalObject = Tru
  terminate Fls = FlsTru
  terminate Tru = IdTru


type instance Product Boolean BF BF = BF
type instance Product Boolean BF BT = BF
type instance Product Boolean BT BF = BF
type instance Product Boolean BT BT = BT

instance HasProducts Boolean where 
  
  product Fls Fls = Fls
  product Fls Tru = Fls
  product Tru Fls = Fls
  product Tru Tru = Tru
  
  proj Fls Fls = (IdFls , IdFls)
  proj Fls Tru = (IdFls , FlsTru)
  proj Tru Fls = (FlsTru, IdFls)
  proj Tru Tru = (IdTru , IdTru)
  
  IdFls  &&& IdFls  = IdFls
  IdFls  &&& FlsTru = IdFls
  FlsTru &&& IdFls  = IdFls
  FlsTru &&& FlsTru = FlsTru
  IdTru  &&& IdTru  = IdTru
  _      &&& _      = error "Other combinations should not type check"


type instance Coproduct Boolean BF BF = BF
type instance Coproduct Boolean BF BT = BT
type instance Coproduct Boolean BT BF = BT
type instance Coproduct Boolean BT BT = BT

instance HasCoproducts Boolean where 
  
  coproduct Fls Fls = Fls
  coproduct Fls Tru = Tru
  coproduct Tru Fls = Tru
  coproduct Tru Tru = Tru
  
  inj Fls Fls = (IdFls , IdFls)
  inj Fls Tru = (FlsTru, IdTru)
  inj Tru Fls = (IdTru , FlsTru)
  inj Tru Tru = (IdTru , IdTru)
  
  IdFls  ||| IdFls  = IdFls
  FlsTru ||| FlsTru = FlsTru
  FlsTru ||| IdTru  = IdTru
  IdTru  ||| FlsTru = IdTru
  IdTru  ||| IdTru  = IdTru
  _      ||| _      = error "Other combinations should not type check"


instance Show (Obj Boolean a) where
  show Fls = "Fls"
  show Tru = "Tru"