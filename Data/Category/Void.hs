{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Void
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- /0/, the empty category. 
-- The limit and colimit of the functor from /0/ to some category provide 
-- terminal and initial objects in that category.
-----------------------------------------------------------------------------
module Data.Category.Void where

import Prelude hiding ((.), id, Functor)
import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation


-- | The (empty) data type of the arrows in /0/. 
data Void a b

magicVoid :: Void a b -> x
magicVoid x = x `seq` error "we never get this far"

magicVoidO :: Obj Void a -> x
magicVoidO x = x `seq` error "we never get this far"


instance Category Void where
  
  -- | The (empty) data type of the objects in /0/. 
  data Obj Void a
  
  src = magicVoid
  tgt = magicVoid
  
  id    = magicVoidO
  a . b = magicVoid (a `seq` b)


-- | The functor from /0/ to (~>), the empty diagram in (~>).
data VoidDiagram ((~>) :: * -> * -> *) = VoidDiagram

type instance Dom (VoidDiagram (~>)) = Void
type instance Cod (VoidDiagram (~>)) = (~>)

instance Category (~>) => Functor (VoidDiagram (~>)) where 
  VoidDiagram % f = magicVoid f


voidNat :: (Functor f, Functor g, Dom f ~ Void, Dom g ~ Void, Cod f ~ d, Cod g ~ d)
  => f -> g -> Nat Void d f g
voidNat f g = Nat f g magicVoidO
