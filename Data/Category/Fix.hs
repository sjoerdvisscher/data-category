{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, StandaloneDeriving, PatternSynonyms, TypeOperators, TypeFamilies, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Fix
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
import Data.Category.CartesianClosed
import Data.Category.Monoidal

import qualified Data.Category.Unit as U
import Data.Category.Coproduct


newtype Fix f a b = Fix (f (Fix f) a b)

-- | @`Fix` f@ is the fixed point category for a category combinator `f`.
deriving instance Category (f (Fix f)) => Category (Fix f)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasInitialObject (f (Fix f)) => HasInitialObject (Fix f) where
  type InitialObject (Fix f) = InitialObject (f (Fix f))
  initialObject = Fix initialObject
  initialize (Fix a) = Fix (initialize a)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasTerminalObject (f (Fix f)) => HasTerminalObject (Fix f) where
  type TerminalObject (Fix f) = TerminalObject (f (Fix f))
  terminalObject = Fix terminalObject
  terminate (Fix a) = Fix (terminate a)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasBinaryProducts (f (Fix f)) => HasBinaryProducts (Fix f) where
  type BinaryProduct (Fix f) x y = BinaryProduct (f (Fix f)) x y
  proj1 (Fix a) (Fix b) = Fix (proj1 a b)
  proj2 (Fix a) (Fix b) = Fix (proj2 a b)
  Fix a &&& Fix b = Fix (a &&& b)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
instance HasBinaryCoproducts (f (Fix f)) => HasBinaryCoproducts (Fix f) where
  type BinaryCoproduct (Fix f) x y = BinaryCoproduct (f (Fix f)) x y
  inj1 (Fix a) (Fix b) = Fix (inj1 a b)
  inj2 (Fix a) (Fix b) = Fix (inj2 a b)
  Fix a ||| Fix b = Fix (a ||| b)

-- | @Fix f@ inherits its exponentials from @f (Fix f)@.
instance CartesianClosed (f (Fix f)) => CartesianClosed (Fix f) where
  type Exponential (Fix f) x y = Exponential (f (Fix f)) x y
  apply (Fix a) (Fix b) = Fix (apply a b)
  tuple (Fix a) (Fix b) = Fix (tuple a b)
  Fix a ^^^ Fix b = Fix (a ^^^ b)

data Wrap (f :: * -> * -> *) = Wrap
-- | The `Wrap` functor wraps `Fix` around @f (Fix f)@.
instance Category (f (Fix f)) => Functor (Wrap (Fix f)) where
  type Dom (Wrap (Fix f)) = f (Fix f)
  type Cod (Wrap (Fix f)) = Fix f
  type Wrap (Fix f) :% a = a
  Wrap % f = Fix f

data Unwrap (f :: * -> * -> *) = Unwrap
-- | The `Unwrap` functor unwraps @Fix f@ to @f (Fix f)@.
instance Category (f (Fix f)) => Functor (Unwrap (Fix f)) where
  type Dom (Unwrap (Fix f)) = Fix f
  type Cod (Unwrap (Fix f)) = f (Fix f)
  type Unwrap (Fix f) :% a = a
  Unwrap % Fix f = f

type WrapTensor f t = Wrap f :.: t :.: (Unwrap f :***: Unwrap f)
-- | @Fix f@ inherits tensor products from @f (Fix f)@.
instance (TensorProduct t, Cod t ~ f (Fix f)) => TensorProduct (WrapTensor (Fix f) t) where
  type Unit (WrapTensor (Fix f) t) = Unit t
  unitObject (_ :.: t :.: _) = Fix (unitObject t)

  leftUnitor (_ :.: t :.: _) (Fix a) = Fix (leftUnitor t a)
  leftUnitorInv (_ :.: t :.: _) (Fix a) = Fix (leftUnitorInv t a)
  rightUnitor (_ :.: t :.: _) (Fix a) = Fix (rightUnitor t a)
  rightUnitorInv (_ :.: t :.: _) (Fix a) = Fix (rightUnitorInv t a)
  associator (_ :.: t :.: _) (Fix a) (Fix b) (Fix c) = Fix (associator t a b c)
  associatorInv (_ :.: t :.: _) (Fix a) (Fix b) (Fix c) = Fix (associatorInv t a b c)

-- | Take the `Omega` category, add a new disctinct object, and an arrow from that object to every object in `Omega`,
--   and you get `Omega` again.
type Omega = Fix ((:>>:) U.Unit)

type Z = I1 ()
type S n = I2 n
pattern Z :: Obj Omega Z
pattern Z = Fix (DC (I1A U.Unit))
pattern S :: Omega a b -> Omega (S a) (S b)
pattern S n = Fix (DC (I2A n))
z2s :: Obj Omega n -> Omega Z (S n)
z2s n = Fix (DC (I12 U.Unit n (Const (\() -> ())) ()))
