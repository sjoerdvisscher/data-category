{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, GADTs, FlexibleContexts, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Comma
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Comma categories.
-----------------------------------------------------------------------------
module Data.Category.Comma where

import Prelude()

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation


data (:/\:) :: * -> * -> * -> * -> * where 
  CommaA :: 
    Obj (t :/\: s) (a, b) ->
    Dom t a a' -> 
    Dom s b b' -> 
    Obj (t :/\: s) (a', b') ->
    (t :/\: s) (a, b) (a', b')

instance (Category (Dom t), Category (Dom s)) => Category (t :/\: s) where
    
  data Obj (t :/\: s) x where
    CommaO :: (Cod t ~ (~>), Cod s ~ (~>))
      => Obj (Dom t) a -> (F t a ~> F s b) -> Obj (Dom s) b -> Obj (t :/\: s) (a, b)
    
  src (CommaA so _ _ _) = so
  tgt (CommaA _ _ _ to) = to
  
  id x@(CommaO a _ b)                     = CommaA x  (id a)   (id b)   x
  (CommaA _ g h to) . (CommaA so g' h' _) = CommaA so (g . g') (h . h') to


type (f `ObjectsFUnder` a) = ConstF f a :/\: f
type (f `ObjectsFOver`  a) = f :/\: ConstF f a

type (c `ObjectsUnder` a) = Id c `ObjectsFUnder` a
type (c `ObjectsOver`  a) = Id c `ObjectsFOver`  a