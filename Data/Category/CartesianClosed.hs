{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, Rank2Types, ScopedTypeVariables, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.CartesianClosed
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.CartesianClosed where
  
import Prelude (($))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Product
import Data.Category.Limit
import Data.Category.Adjunction
import qualified Data.Category.Monoidal as M


type family Exponential (~>) y z :: *

class (HasTerminalObject (~>), HasBinaryProducts (~>)) => CartesianClosed (~>) where
  
  apply :: Obj (~>) y -> Obj (~>) z -> BinaryProduct (~>) (Exponential (~>) y z) y ~> z
  tuple :: Obj (~>) y -> Obj (~>) z -> z ~> Exponential (~>) y (BinaryProduct (~>) z y)
  (^^^) :: (z1 ~> z2) -> (y2 ~> y1) -> (Exponential (~>) y1 z1 ~> Exponential (~>) y2 z2)


data ExpFunctor ((~>) :: * -> * -> *) = ExpFunctor
type instance Dom (ExpFunctor (~>)) = Op (~>) :**: (~>)
type instance Cod (ExpFunctor (~>)) = (~>)
type instance (ExpFunctor (~>)) :% (y, z) = Exponential (~>) y z
instance CartesianClosed (~>) => Functor (ExpFunctor (~>)) where
  ExpFunctor % (Op y :**: z) = z ^^^ y



type instance Exponential (->) y z = y -> z

instance (CartesianClosed (->)) where
  
  apply _ _ (f, y) = f y
  tuple _ _ z      = \y -> (z, y)
  f ^^^ h          = \g -> f . g . h



data CatApply (y :: * -> * -> *) (z :: * -> * -> *) = CatApply
type instance Dom (CatApply y z) = Nat y z :**: y
type instance Cod (CatApply y z) = z
type instance CatApply y z :% (f, a) = f :% a
instance (Category y, Category z) => Functor (CatApply y z) where
  CatApply % (l :**: r) = catApply l r
    where
      catApply :: Nat y z f g -> y a b -> z (f :% a) (g :% b)
      catApply n@Nat{} h = n ! h

data CatTuple (y :: * -> * -> *) (z :: * -> * -> *) = CatTuple
type instance Dom (CatTuple y z) = z
type instance Cod (CatTuple y z) = Nat y (z :**: y)
type instance CatTuple y z :% a = Tuple1 z y a
instance (Category y, Category z) => Functor (CatTuple y z) where
  CatTuple % f = Nat (Tuple1 (src f)) (Tuple1 (tgt f)) $ \z -> f :**: z


type instance Exponential Cat (CatW c) (CatW d) = CatW (Nat c d)

instance (CartesianClosed Cat) where
  
  apply CatA{} CatA{}   = CatA CatApply
  tuple CatA{} CatA{}   = CatA CatTuple
  (CatA f) ^^^ (CatA h) = CatA (Wrap f h)



data ProductWith (~>) y = ProductWith (Obj (~>) y)
type instance Dom (ProductWith (~>) y) = (~>)
type instance Cod (ProductWith (~>) y) = (~>)
type instance ProductWith (~>) y :% z = ProductFunctor (~>) :% (z, y)
instance HasBinaryProducts (~>) => Functor (ProductWith (~>) y) where
  ProductWith y % f = f *** y
  
data ExponentialWith (~>) y = ExponentialWith (Obj (~>) y)
type instance Dom (ExponentialWith (~>) y) = (~>)
type instance Cod (ExponentialWith (~>) y) = (~>)
type instance ExponentialWith (~>) y :% z = Exponential (~>) y z
instance CartesianClosed (~>) => Functor (ExponentialWith (~>) y) where
  ExponentialWith y % f = f ^^^ y

curryAdj :: CartesianClosed (~>) => Obj (~>) y -> Adjunction (~>) (~>) (ProductWith (~>) y) (ExponentialWith (~>) y)
curryAdj y = mkAdjunction (ProductWith y) (ExponentialWith y) (tuple y) (apply y)

curry :: CartesianClosed (~>) => Obj (~>) x -> Obj (~>) y -> Obj (~>) z -> (ProductWith (~>) y :% x) ~> z -> x ~> (ExponentialWith (~>) y :% z)
curry x y _ = leftAdjunct (curryAdj y) x

uncurry :: CartesianClosed (~>) => Obj (~>) x -> Obj (~>) y -> Obj (~>) z -> x ~> (ExponentialWith (~>) y :% z) -> (ProductWith (~>) y :% x) ~> z
uncurry _ y z = rightAdjunct (curryAdj y) z


type State (~>) s a = ExponentialWith (~>) s :% ProductWith (~>) s :% a

stateMonadReturn :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> a ~> State (~>) s a
stateMonadReturn s a = M.unit (adjunctionMonad $ curryAdj s) ! a

stateMonadJoin :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> State (~>) s (State (~>) s a) ~> State (~>) s a
stateMonadJoin s a = M.multiply (adjunctionMonad $ curryAdj s) ! a

type Context (~>) s a = ProductWith (~>) s :% ExponentialWith (~>) s :% a

contextComonadExtract :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> Context (~>) s a ~> a
contextComonadExtract s a = M.counit (adjunctionComonad $ curryAdj s) ! a

contextComonadDuplicate :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> Context (~>) s a ~> Context (~>) s (Context (~>) s a)
contextComonadDuplicate s a = M.comultiply (adjunctionComonad $ curryAdj s) ! a
