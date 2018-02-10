{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, PatternSynonyms, TypeOperators, TypeFamilies, UndecidableInstances, NoImplicitPrelude #-}
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
import Data.Category.CartesianClosed

import Data.Category.Unit
import Data.Category.Coproduct


newtype Fix f a b = Fix (f (Fix f) a b) 

-- | @`Fix` f@ is the fixed point category for a category combinator `f`.
deriving instance Category (f (Fix f)) => Category (Fix f)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
deriving instance HasInitialObject (f (Fix f)) => HasInitialObject (Fix f)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
deriving instance HasTerminalObject (f (Fix f)) => HasTerminalObject (Fix f)

-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
deriving instance HasBinaryProducts (f (Fix f)) => HasBinaryProducts (Fix f)
  
-- | @Fix f@ inherits its (co)limits from @f (Fix f)@.
deriving instance HasBinaryCoproducts (f (Fix f)) => HasBinaryCoproducts (Fix f)

-- | @Fix f@ inherits its exponentials from @f (Fix f)@.
deriving instance CartesianClosed (f (Fix f)) => CartesianClosed (Fix f)
  
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

type Z = I1 ()
type S n = I2 n
pattern Z :: Obj Omega Z
pattern Z = Fix (DC (I1A Unit))
pattern S :: Omega a b -> Omega (S a) (S b)
pattern S n = Fix (DC (I2A n))
z2s :: Obj Omega n -> Omega Z (S n)
z2s n = Fix (DC (I12 Unit n (Const (\() -> ())) ()))
