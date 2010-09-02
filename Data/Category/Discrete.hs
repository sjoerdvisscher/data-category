{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, EmptyDataDecls, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Discrete
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

import Prelude hiding ((.), id, Functor, product)

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Void
import Data.Category.Pair

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


magicZ :: Discrete Z a b -> x
magicZ x = x `seq` error "we never get this far"

magicZO :: Obj (Discrete Z) a -> x
magicZO x = x `seq` error "we never get this far"



instance Category (Discrete Z) where
  
  data Obj (Discrete Z) a
  
  src = magicZ
  tgt = magicZ
  
  id    = magicZO
  a . b = magicZ (a `seq` b)



data Next :: * -> * -> * where
  Next :: (Functor f, Dom f ~ Discrete (S n)) => f -> Next n f
  
type instance Dom (Next n f) = Discrete n
type instance Cod (Next n f) = Cod f
type instance Next n f :% a = f :% S a

instance (Functor f, Category (Discrete n)) => Functor (Next n f) where
  Next f % IdZ       = f % StepS IdZ
  Next f % (StepS a) = f % StepS (StepS a)
    

infixr 7 :::

data DiscreteDiagram :: (* -> * -> *) -> * -> * -> * where
  Nil   :: DiscreteDiagram (~>) Z ()
  (:::) :: Obj (~>) x -> DiscreteDiagram (~>) n xs -> DiscreteDiagram (~>) (S n) (x, xs)
  
type instance Dom (DiscreteDiagram (~>) n xs) = Discrete n
type instance Cod (DiscreteDiagram (~>) n xs) = (~>)
type instance DiscreteDiagram (~>) (S n) (x, xs) :% Z = x
type instance DiscreteDiagram (~>) (S n) (x, xs) :% (S a) = DiscreteDiagram (~>) n xs :% a

instance (Category (~>)) 
  => Functor (DiscreteDiagram (~>) Z ()) where
  Nil        % f = magicZ f

instance (Category (~>), Category (Discrete n), Functor (DiscreteDiagram (~>) n xs)) 
  => Functor (DiscreteDiagram (~>) (S n) (x, xs)) where
  (x ::: _)  % IdZ = id x
  (_ ::: xs) % StepS n = xs % n
