{-# LANGUAGE TypeFamilies, GADTs, EmptyDataDecls, FlexibleContexts, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Omega
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Discrete n, the category with n objects, and as the only arrows their identities.
-----------------------------------------------------------------------------
module Data.Category.Discrete where

import Prelude hiding ((.), id, Functor)

import Data.Category


data Z
data S n = S n

-- | The arrows in Discrete n, a finite set of identity arrows.
data Discrete :: * -> * -> * -> * where
  IdZ   :: Discrete (S n) Z Z
  StepS :: Discrete n a a -> Discrete (S n) (S a) (S a)

instance Category (Discrete n) => Category (Discrete (S n)) where
  
  data Obj (Discrete (S n)) a where
    OZ :: Obj (Discrete (S n)) Z
    OS :: Obj (Discrete n) o -> Obj (Discrete (S n)) (S o)
    
  src IdZ       = OZ
  src (StepS a) = OS $ src a
  
  tgt IdZ       = OZ
  tgt (StepS a) = OS $ tgt a
  
  id OZ             = IdZ
  id (OS n)         = StepS $ id n
  
  IdZ     . IdZ     = IdZ
  StepS a . StepS b = StepS (a . b)
  _       . _       = error "Other combinations should not type-check."
