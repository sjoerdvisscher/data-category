{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, Rank2Types, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Void
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.CartesianClosed where
  
import Prelude (($), undefined)

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Product
import Data.Category.Limit
import Data.Category.Adjunction
import qualified Data.Category.Monoidal as M


class (HasTerminalObject (~>), HasBinaryProducts (~>)) => CartesianClosed (~>) where
  
  type Exponential (~>) :: *
  
  eval  :: Obj (~>) y -> Obj (~>) z -> (ProductFunctor (~>) :% (Exponential (~>) :% (y, z), y)) ~> z
  tuple :: Obj (~>) y -> Obj (~>) z -> z ~> (Exponential (~>) :% (y, ProductFunctor (~>) :% (z, y)))


data ProductWith (~>) y = ProductWith (Obj (~>) y)
type instance Dom (ProductWith (~>) y) = (~>)
type instance Cod (ProductWith (~>) y) = (~>)
type instance ProductWith (~>) y :% z = ProductFunctor (~>) :% (z, y)
instance HasBinaryProducts (~>) => Functor (ProductWith (~>) y) where
  ProductWith y % f = f *** y
  
data ExponentialWith (~>) y = ExponentialWith (Obj (~>) y)
type instance Dom (ExponentialWith (~>) y) = (~>)
type instance Cod (ExponentialWith (~>) y) = (~>)
type instance ExponentialWith (~>) y :% z = Exponential (~>) :% (y, z)
instance CartesianClosed (~>) => Functor (ExponentialWith (~>) y) where
  ExponentialWith y % f = undefined
  


instance (CartesianClosed (->)) where
  
  type Exponential (->) = Hom (->)
  
  eval  _ _ (f, y) = f y
  tuple _ _ z = \y -> (z, y)



data CatEval (y :: * -> * -> *) (z :: * -> * -> *) = CatEval
type instance Dom (CatEval y z) = Nat y z :**: y
type instance Cod (CatEval y z) = z
type instance CatEval y z :% (f, a) = f :% a
instance (Category y, Category z) => Functor (CatEval y z) where
  CatEval % (l :**: r) = catEval l r
    where
      catEval :: (Category y, Category z) => Nat y z f g -> y a b -> z (f :% a) (g :% b)
      catEval (Nat f _ n) h = n (tgt h) . f % h -- g % h . n (src h)

data CatTuple (y :: * -> * -> *) (z :: * -> * -> *) = CatTuple
type instance Dom (CatTuple y z) = z
type instance Cod (CatTuple y z) = Nat y (z :**: y)
type instance CatTuple y z :% a = Tuple1 z y a
instance (Category y, Category z) => Functor (CatTuple y z) where
  CatTuple % f = Nat (Tuple1 (src f)) (Tuple1 (tgt f)) $ \z -> f :**: z


instance (CartesianClosed Cat) where
  
  type Exponential Cat = CatExponential
  
  eval  CatA{} CatA{} = CatA CatEval
  tuple CatA{} CatA{} = CatA CatTuple



curryAdj :: CartesianClosed (~>) => Obj (~>) y -> Adjunction (~>) (~>) (ProductWith (~>) y) (ExponentialWith (~>) y)
curryAdj y = mkAdjunction (ProductWith y) (ExponentialWith y) (tuple y) (eval y)

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