{-# LANGUAGE TypeFamilies, GADTs, RankNTypes, PolyKinds, LinearTypes, FlexibleInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category (

  -- * Category
    Category(..)
  , Obj
  , Kind

  -- * Opposite category
  , Op(..)

  -- * `(->)`/Hask
  , obj

) where

import GHC.Exts
import Data.Kind (Type)

infixr 8 .

-- | Whenever objects are required at value level, they are represented by their identity arrows.
type Obj k a = k a a

-- | An instance of @Category k@ declares the arrow @k@ as a category.
class Category k where

  src :: k a b -> Obj k a
  tgt :: k a b -> Obj k b

  (.) :: k b c -> k a b -> k a c


obj :: Obj (FUN m) a
obj x = x

-- | For @m ~ Many@: The category with Haskell types as objects and Haskell functions as arrows, i.e. @(->)@.
-- For @m ~ One@: The category with Haskell types as objects and Haskell linear functions as arrows, i.e. @(%1->)@.
instance Category (FUN m) where

  src _ = obj
  tgt _ = obj

  f . g = \x -> f (g x)


newtype Op k a b = Op { unOp :: k b a }

-- | @Op k@ is opposite category of the category @k@.
instance Category k => Category (Op k) where

  src (Op a)      = Op (tgt a)
  tgt (Op a)      = Op (src a)

  (Op a) . (Op b) = Op (b . a)


-- | @Kind k@ is the kind of the objects of the category @k@.
type family Kind (k :: o -> o -> Type) :: Type where
  Kind (k :: o -> o -> Type) = o
