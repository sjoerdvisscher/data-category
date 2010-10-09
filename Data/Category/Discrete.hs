{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, RankNTypes, EmptyDataDecls, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
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

type Void = Discrete Z
type Unit = Discrete (S Z)
type Pair = Discrete (S (S Z))

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
    
nextNat :: forall n f g d. Category (Discrete n) 
  => Nat (Discrete (S n)) d f g
  -> Nat (Discrete n) d (Next n f) (Next n g)
nextNat (Nat f g n) = Nat (Next f) (Next g) n'
  where
    n' :: forall i. Obj (Discrete n) i -> Component (Next n f) (Next n g) i
    n' Z = n (S Z)
    n' (S x) = n (S (S x))


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


voidNat :: (Functor f, Functor g, Dom f ~ Void, Dom g ~ Void, Cod f ~ d, Cod g ~ d)
  => f -> g -> Nat Void d f g
voidNat f g = Nat f g magicZ


pairNat :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
  => f -> g -> Com f g Z -> Com f g (S Z) -> Nat Pair d f g
pairNat f g c1 c2 = Nat f g (\x -> unCom $ n c1 c2 x) where
  n :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
    => Com f g Z -> Com f g (S Z) -> Obj Pair a -> Com f g a
  n c _ Z = c
  n _ c (S Z) = c
  n _ _ (S (S _)) = error "Other combinations should not type-check."


type PairDiagram (~>) x y = DiscreteDiagram (~>) (S (S Z)) (x, (y, ()))

arrowPair :: Category (~>) => (x1 ~> x2) -> (y1 ~> y2) -> Nat Pair (~>) (PairDiagram (~>) x1 y1) (PairDiagram (~>) x2 y2)
arrowPair l r = pairNat (src l ::: src r ::: Nil) (tgt l ::: tgt r ::: Nil) (Com l) (Com r)

