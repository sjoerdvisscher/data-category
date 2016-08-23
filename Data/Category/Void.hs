{-# LANGUAGE EmptyCase, LambdaCase, TypeOperators, GADTs, TypeFamilies, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Void
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Void where

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation


data Void a b

magic :: Void a b -> x
magic = \case { }

-- | `Void` is the category with no objects.
instance Category Void where

  src = magic
  tgt = magic

  (.) = magic


voidNat :: (Functor f, Functor g, Dom f ~ Void, Dom g ~ Void, Cod f ~ d, Cod g ~ d)
  => f -> g -> Nat Void d f g
voidNat f g = Nat f g magic


data Magic (k :: * -> * -> *) = Magic
-- | Since there is nothing to map in `Void`, there's a functor from it to any other category.
instance Category k => Functor (Magic k) where
  type Dom (Magic k) = Void
  type Cod (Magic k) = k

  Magic % f = magic f
