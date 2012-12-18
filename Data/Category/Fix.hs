{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances, NoImplicitPrelude #-}
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

-- | @`Fix` f@ is the fixed point category for a category combinator `f`.
instance Category (f (Fix f)) => Category (Fix f) where
  src (Fix a) = Fix (src a)
  tgt (Fix a) = Fix (tgt a)
  Fix a . Fix b = Fix (a . b)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasInitialObject (f (Fix f)) => HasInitialObject (Fix f) where
  type InitialObject (Fix f) = InitialObject (f (Fix f))
  initialObject = Fix initialObject
  initialize (Fix o) = Fix (initialize o)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasTerminalObject (f (Fix f)) => HasTerminalObject (Fix f) where
  type TerminalObject (Fix f) = TerminalObject (f (Fix f))
  terminalObject = Fix terminalObject
  terminate (Fix o) = Fix (terminate o)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasBinaryProducts (f (Fix f)) => HasBinaryProducts (Fix f) where
  type BinaryProduct (Fix f) a b = BinaryProduct (f (Fix f)) a b
  proj1 (Fix a) (Fix b) = Fix (proj1 a b)
  proj2 (Fix a) (Fix b) = Fix (proj2 a b)
  Fix a &&& Fix b = Fix (a &&& b)
  
-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasBinaryCoproducts (f (Fix f)) => HasBinaryCoproducts (Fix f) where
  type BinaryCoproduct (Fix f) a b = BinaryCoproduct (f (Fix f)) a b
  inj1 (Fix a) (Fix b) = Fix (inj1 a b)
  inj2 (Fix a) (Fix b) = Fix (inj2 a b)
  Fix a ||| Fix b = Fix (a ||| b)

data Wrap (f :: (* -> * -> *) -> * -> * -> *) = Wrap
-- | The `Wrap` functor wraps `Fix` around @f (Fix f)@.
instance Category (f (Fix f)) => Functor (Wrap f) where
  type Dom (Wrap f) = f (Fix f)
  type Cod (Wrap f) = Fix f
  type Wrap f :% a = a
  Wrap % f = Fix f

-- | Take the `Omega` category, add a new disctinct object, and an arrow from that object to every object in `Omega`,
--   and you get `Omega` again.
type Omega = Fix ((:>>:) Unit)
