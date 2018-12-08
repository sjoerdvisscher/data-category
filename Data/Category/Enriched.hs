{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , FlexibleContexts
  , NoImplicitPrelude
  , AllowAmbiguousTypes
  , UndecidableInstances
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Enriched
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Enriched where

import Data.Category
import Data.Category.Functor
import Data.Category.Limit
import Data.Category.Monoidal
import Data.Category.CartesianClosed
import Data.Category.Boolean

-- | An enriched category
class (TensorProduct (Tensor k)) => EnrichedCat (k :: * -> * -> *) where
  -- | The tensor product of the category V which k is enriched in
  type Tensor k :: *

  -- | The hom object in V from a to b
  type H k a b :: *

  id :: (v ~ Cod (Tensor k), i ~ Unit (Tensor k)) => Obj k a -> v i (H k a a)
  comp :: (v ~ Cod (Tensor k)) => Obj k a -> Obj k b -> Obj k c -> v (Tensor k :% (H k b c, H k a b)) (H k a c)


newtype Self k a b = Self (k a b)
-- | A cartesian closed category can be enriched in itself
instance CartesianClosed k => EnrichedCat (Self k) where
  type Tensor (Self k) = ProductFunctor k
  type H (Self k) a b = Exponential k a b
  id (Self a) = curry (unitObject ProductFunctor) a a (leftUnitor ProductFunctor a)
  comp (Self a) (Self b) (Self c) = curry (bc *** ab) a c (apply b c . (bc *** apply a b) . associator ProductFunctor bc ab a)
    where
      bc = c ^^^ b
      ab = b ^^^ a

data One
data Two
data Three
data PosetTest a b where
  One :: PosetTest One One
  Two :: PosetTest Two Two
  Three :: PosetTest Three Three
instance EnrichedCat PosetTest where
  type Tensor PosetTest = ProductFunctor Boolean
  type H PosetTest One One = Tru
  type H PosetTest One Two = Tru
  type H PosetTest One Three = Tru
  type H PosetTest Two One = Fls
  type H PosetTest Two Two = Tru
  type H PosetTest Two Three = Tru
  type H PosetTest Three One = Fls
  type H PosetTest Three Two = Fls
  type H PosetTest Three Three = Tru

  id One = Tru
  id Two = Tru
  id Three = Tru
  comp One One One = Tru
  comp One One Two = Tru
  comp One One Three = Tru
  comp One Two One = F2T
  comp One Two Two = Tru
  comp One Two Three = Tru
  comp One Three One = F2T
  comp One Three Two = F2T
  comp One Three Three = Tru
  comp Two One One = Fls
  comp Two One Two = F2T
  comp Two One Three = F2T
  comp Two Two One = Fls
  comp Two Two Two = Tru
  comp Two Two Three = Tru
  comp Two Three One = Fls
  comp Two Three Two = F2T
  comp Two Three Three = Tru
  comp Three One One = Fls
  comp Three One Two = Fls
  comp Three One Three = F2T
  comp Three Two One = Fls
  comp Three Two Two = Fls
  comp Three Two Three = F2T
  comp Three Three One = Fls
  comp Three Three Two = Fls
  comp Three Three Three = Tru