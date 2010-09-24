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


data Z
data S n

-- | The arrows in Discrete n, a finite set of identity arrows.
data Discrete :: * -> * -> * -> * where
  Z :: Discrete (S n) Z Z
  S :: Discrete n a a -> Discrete (S n) (S a) (S a)


magicZ :: Discrete Z a b -> x
magicZ x = x `seq` error "we never get this far"


instance Category (Discrete Z) where
  
  src   = magicZ
  tgt   = magicZ
  
  a . b = magicZ (a `seq` b)


instance Category (Discrete n) => Category (Discrete (S n)) where
  
  src Z     = Z
  src (S a) = S $ src a
  
  tgt Z     = Z
  tgt (S a) = S $ tgt a
  
  Z   . Z   = Z
  S a . S b = S (a . b)
  _   . _   = error "Other combinations should not type-check."



data Next :: * -> * -> * where
  Next :: (Functor f, Dom f ~ Discrete (S n)) => f -> Next n f
  
type instance Dom (Next n f) = Discrete n
type instance Cod (Next n f) = Cod f
type instance Next n f :% a = f :% S a

instance (Functor f, Category (Discrete n)) => Functor (Next n f) where
  Next f % Z     = f % S Z
  Next f % (S a) = f % S (S a)
    

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
  (x ::: _)  % Z   = x
  (_ ::: xs) % S n = xs % n
