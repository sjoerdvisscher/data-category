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


data CommaO :: * -> * -> * -> * where
  CommaO :: (Cod t ~ (~>), Cod s ~ (~>))
    => Obj (Dom t) a -> (t :% a ~> s :% b) -> Obj (Dom s) b -> CommaO t s (a, b)
    
data (:/\:) :: * -> * -> * -> * -> * where 
  CommaA :: 
    CommaO t s (a, b) ->
    Dom t a a' -> 
    Dom s b b' -> 
    CommaO t s (a', b') ->
    (t :/\: s) (a, b) (a', b')

instance (Category (Dom t), Category (Dom s)) => Category (t :/\: s) where
    
  src (CommaA so@(CommaO a _ b) _ _ _)    = CommaA so a        b        so
  tgt (CommaA _ _ _ to@(CommaO a _ b))    = CommaA to a        b        to
  
  (CommaA _ g h to) . (CommaA so g' h' _) = CommaA so (g . g') (h . h') to


type (f `ObjectsFUnder` a) = ConstF f a :/\: f
type (f `ObjectsFOver`  a) = f :/\: ConstF f a

type (c `ObjectsUnder` a) = Id c `ObjectsFUnder` a
type (c `ObjectsOver`  a) = Id c `ObjectsFOver`  a