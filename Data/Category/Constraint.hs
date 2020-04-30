{-# LANGUAGE
    GADTs
  , DataKinds
  , RankNTypes
  , TypeFamilies
  , TypeOperators
  , KindSignatures
  , ConstraintKinds
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , QuantifiedConstraints
  , MultiParamTypeClasses
  , UndecidableSuperClasses
  , NoImplicitPrelude
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Constraint
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Constraint where

import Data.Category
import Data.Category.Limit
import Data.Category.CartesianClosed

import Data.Kind (Constraint)
import GHC.Exts (Any)

data Dict :: Constraint -> * where
  Dict :: a => Dict a

-- | Code mostly stolen from the constraints package
newtype a :- b = Sub (a => Dict b)

id :: a :- a
id = Sub Dict

instance Category (:-) where
  src _ = id
  tgt _ = id
  Sub c . Sub b = Sub (case b of Dict -> c)

class Any => Bottom where
  no :: a
instance HasInitialObject (:-) where
  type InitialObject (:-) = Bottom
  initialObject = id
  initialize _ = Sub no

instance HasTerminalObject (:-) where
  type TerminalObject (:-) = () :: Constraint
  terminalObject = id
  terminate _ = Sub Dict

instance HasBinaryProducts (:-) where
  type BinaryProduct (:-) a b = (a, b) :: Constraint
  proj1 _ _ = Sub Dict
  proj2 _ _ = Sub Dict
  Sub a &&& Sub b = Sub (case (a, b) of (Dict, Dict) -> Dict)

class (a => b) => a :=>: b where ins :: a :- b
instance (a => b) => a :=>: b where ins = Sub Dict

instance CartesianClosed (:-) where
  type Exponential (:-) a b = a :=>: b
  apply _ _ = Sub Dict
  tuple _ _ = Sub Dict
  a ^^^ b = a ^^^ b -- TODO: Sub (toDict (a . ins . b)) where toDict :: (a :- b) -> Dict (a :=>: b)
