{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, RankNTypes, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
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
module Data.Category.Discrete (

  -- * Discrete Categories
    Discrete(..)
  , Z, S
  , Void
  , Unit
  , Pair
  
  -- * Diagrams
  , DiscreteDiagram(..)
  , PairDiagram
  , arrowPair
    
  -- * Natural Transformations
  , discreteNat
  , ComList(..)
  , voidNat
  , pairNat
    
) where

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


-- | @Discrete Z@ is the discrete category with no objects.
instance Category (Discrete Z) where
  
  src   = magicZ
  tgt   = magicZ
  
  a . b = magicZ (a `seq` b)


-- | @Discrete (S n)@ is the discrete category with one object more than @Discrete n@.
instance Category (Discrete n) => Category (Discrete (S n)) where
  
  src Z     = Z
  src (S a) = S $ src a
  
  tgt Z     = Z
  tgt (S a) = S $ tgt a
  
  Z   . Z   = Z
  S a . S b = S (a . b)
  _   . _   = error "Other combinations should not type-check."


-- | @Void@ is the empty category.
type Void = Discrete Z
-- | @Unit@ is the discrete category with one object.
type Unit = Discrete (S Z)
-- | @Pair@ is the discrete category with two objects.
type Pair = Discrete (S (S Z))


type family PredDiscrete (c :: * -> * -> *) :: * -> * -> *
type instance PredDiscrete (Discrete (S n)) = Discrete n

data Next :: * -> * where
  Next :: (Functor f, Dom f ~ Discrete (S n)) => f -> Next f
  
type instance Dom (Next f) = PredDiscrete (Dom f)
type instance Cod (Next f) = Cod f
type instance Next f :% a = f :% S a

instance (Functor f, Category (PredDiscrete (Dom f))) => Functor (Next f) where
  Next f % Z     = f % S Z
  Next f % (S a) = f % S (S a)


infixr 7 :::

-- | The functor from @Discrete n@ to @(~>)@, a diagram of @n@ objects in @(~>)@. 
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


infixr 7 ::::

data ComList f g n z where
  ComNil :: ComList f g Z z
  (::::) :: Com f g z -> ComList f g n (S z) -> ComList f g (S n) z

class DiscreteNat n where
  discreteNat :: (Functor f, Functor g, Category d, Dom f ~ Discrete n, Dom g ~ Discrete n, Cod f ~ d, Cod g ~ d)
    => f -> g -> ComList f g n Z -> Nat (Discrete n) d f g
  shiftComList :: ComList f g n (S z) -> ComList (Next f) (Next g) n z
  
instance DiscreteNat Z where
  discreteNat f g ComNil = Nat f g magicZ
  shiftComList ComNil = ComNil

instance (Category (Discrete n), DiscreteNat n) => DiscreteNat (S n) where
  discreteNat f g comlist = Nat f g (\x -> unCom $ h f g comlist x) where
    h :: (Functor f, Functor g, Category d, Dom f ~ Discrete (S n), Dom g ~ Discrete (S n), Cod f ~ d, Cod g ~ d)
      => f -> g -> ComList f g (S n) Z -> Obj (Discrete (S n)) a -> Com f g a
    h _  _  (c :::: _ ) Z     = c
    h f' g' (_ :::: cs) (S n) = Com $ (discreteNat (Next f') (Next g') (shiftComList cs)) ! n
  shiftComList (Com c :::: cs) = Com c :::: shiftComList cs

voidNat :: (Functor f, Functor g, Category d, Dom f ~ Void, Dom g ~ Void, Cod f ~ d, Cod g ~ d)
  => f -> g -> Nat Void d f g
voidNat f g       = discreteNat f g ComNil

pairNat :: (Functor f, Functor g, Category d, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
  => f -> g -> Com f g Z -> Com f g (S Z) -> Nat Pair d f g
pairNat f g c1 c2 = discreteNat f g (c1 :::: c2 :::: ComNil)


-- | The functor from @Pair@ to @(~>)@, a diagram of 2 objects in @(~>)@. 
type PairDiagram (~>) x y = DiscreteDiagram (~>) (S (S Z)) (x, (y, ()))

arrowPair :: Category (~>) => (x1 ~> x2) -> (y1 ~> y2) -> Nat Pair (~>) (PairDiagram (~>) x1 y1) (PairDiagram (~>) x2 y2)
arrowPair l r = pairNat (src l ::: src r ::: Nil) (tgt l ::: tgt r ::: Nil) (Com l) (Com r)

