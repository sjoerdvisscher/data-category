{-# LANGUAGE TypeFamilies, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.AddObject
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Fix where
  
import Data.Category
import Data.Category.Functor
import Data.Category.Limit

import Data.Category.Unit
import Data.Category.Coproduct


newtype Fix f a b = Fix (f (Fix f) a b)

-- | `Fix f` is the fixed point category for a category combinator `f`.
instance Category (f (Fix f)) => Category (Fix f) where
  src (Fix a) = Fix (src a)
  tgt (Fix a) = Fix (tgt a)
  Fix a . Fix b = Fix (a . b)

instance HasInitialObject (f (Fix f)) => HasInitialObject (Fix f) where
  type InitialObject (Fix f) = InitialObject (f (Fix f))
  initialObject = Fix initialObject
  initialize (Fix o) = Fix (initialize o)

instance HasTerminalObject (f (Fix f)) => HasTerminalObject (Fix f) where
  type TerminalObject (Fix f) = TerminalObject (f (Fix f))
  terminalObject = Fix terminalObject
  terminate (Fix o) = Fix (terminate o)

type instance BinaryProduct (Fix f) a b = BinaryProduct (f (Fix f)) a b
instance HasBinaryProducts (f (Fix f)) => HasBinaryProducts (Fix f) where
  proj1 (Fix a) (Fix b) = Fix (proj1 a b)
  proj2 (Fix a) (Fix b) = Fix (proj2 a b)
  Fix a &&& Fix b = Fix (a &&& b)
  
type instance BinaryCoproduct (Fix f) a b = BinaryCoproduct (f (Fix f)) a b
instance HasBinaryCoproducts (f (Fix f)) => HasBinaryCoproducts (Fix f) where
  inj1 (Fix a) (Fix b) = Fix (inj1 a b)
  inj2 (Fix a) (Fix b) = Fix (inj2 a b)
  Fix a ||| Fix b = Fix (a ||| b)

data Wrap (f :: (* -> * -> *) -> * -> * -> *) = Wrap
type instance Dom (Wrap f) = f (Fix f)
type instance Cod (Wrap f) = Fix f
type instance Wrap f :% a = a
instance Category (f (Fix f)) => Functor (Wrap f) where
  Wrap % f = Fix f
  
type Omega = Fix ((:>>:) Unit)
