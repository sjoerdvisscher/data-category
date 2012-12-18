{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, Rank2Types, ScopedTypeVariables, UndecidableInstances, TypeSynonymInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.CartesianClosed
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.CartesianClosed where
  
import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Product
import Data.Category.Limit
import Data.Category.Adjunction
import Data.Category.Monoidal as M


-- | A category is cartesian closed if it has all products and exponentials for all objects.
class (HasTerminalObject k, HasBinaryProducts k) => CartesianClosed k where
  type Exponential k y z :: *
  
  apply :: Obj k y -> Obj k z -> k (BinaryProduct k (Exponential k y z) y) z
  tuple :: Obj k y -> Obj k z -> k z (Exponential k y (BinaryProduct k z y))
  (^^^) :: k z1 z2 -> k y2 y1 -> k (Exponential k y1 z1) (Exponential k y2 z2)


data ExpFunctor (k :: * -> * -> *) = ExpFunctor
-- | The exponential as a bifunctor.
instance CartesianClosed k => Functor (ExpFunctor k) where
  type Dom (ExpFunctor k) = Op k :**: k
  type Cod (ExpFunctor k) = k
  type (ExpFunctor k) :% (y, z) = Exponential k y z

  ExpFunctor % (Op y :**: z) = z ^^^ y


-- | Exponentials in @Hask@ are functions.
instance CartesianClosed (->) where
  type Exponential (->) y z = y -> z
  
  apply _ _ (f, y) = f y
  tuple _ _ z      = \y -> (z, y)
  f ^^^ h          = \g -> f . g . h



data Apply (y :: * -> * -> *) (z :: * -> * -> *) = Apply
-- | 'Apply' is a bifunctor, @Apply :% (f, a)@ applies @f@ to @a@, i.e. @f :% a@.
instance (Category y, Category z) => Functor (Apply y z) where
  type Dom (Apply y z) = Nat y z :**: y
  type Cod (Apply y z) = z
  type Apply y z :% (f, a) = f :% a
  Apply % (l :**: r) = l ! r

data ToTuple1 (y :: * -> * -> *) (z :: * -> * -> *) = ToTuple1
-- | 'ToTuple1' converts an object @a@ to the functor 'Tuple1' @a@.
instance (Category y, Category z) => Functor (ToTuple1 y z) where
  type Dom (ToTuple1 y z) = z
  type Cod (ToTuple1 y z) = Nat y (z :**: y)
  type ToTuple1 y z :% a = Tuple1 z y a
  ToTuple1 % f = Nat (Tuple1 (src f)) (Tuple1 (tgt f)) (\z -> f :**: z)

data ToTuple2 (y :: * -> * -> *) (z :: * -> * -> *) = ToTuple2
-- | 'ToTuple2' converts an object @a@ to the functor 'Tuple2' @a@.
instance (Category y, Category z) => Functor (ToTuple2 y z) where
  type Dom (ToTuple2 y z) = y
  type Cod (ToTuple2 y z) = Nat z (z :**: y)
  type ToTuple2 y z :% a = Tuple2 z y a
  ToTuple2 % f = Nat (Tuple2 (src f)) (Tuple2 (tgt f)) (\y -> y :**: f)


-- | Exponentials in @Cat@ are the functor categories.
instance CartesianClosed Cat where
  type Exponential Cat (CatW c) (CatW d) = CatW (Nat c d)
  
  apply CatA{} CatA{}   = CatA Apply
  tuple CatA{} CatA{}   = CatA ToTuple1
  (CatA f) ^^^ (CatA h) = CatA (Wrap f h)


-- | The product functor is left adjoint the the exponential functor.
curryAdj :: CartesianClosed k
         => Obj k y
         -> Adjunction k k
              (ProductFunctor k :.: Tuple2 k k y)
              (ExpFunctor k :.: Tuple1 (Op k) k y)
curryAdj y = mkAdjunction (ProductFunctor :.: Tuple2 y) (ExpFunctor :.: Tuple1 (Op y)) (tuple y) (apply y)

-- | From the adjunction between the product functor and the exponential functor we get the curry and uncurry functions,
--   generalized to any cartesian closed category.
curry :: CartesianClosed k => Obj k x -> Obj k y -> Obj k z -> k (BinaryProduct k x y) z -> k x (Exponential k y z)
curry x y _ = leftAdjunct (curryAdj y) x

uncurry :: CartesianClosed k => Obj k x -> Obj k y -> Obj k z -> k x (Exponential k y z) -> k (BinaryProduct k x y) z
uncurry _ y z = rightAdjunct (curryAdj y) z

-- | From every adjunction we get a monad, in this case the State monad.
type State k s a = Exponential k s (BinaryProduct k a s)

stateMonadReturn :: CartesianClosed k => Obj k s -> Obj k a -> k a (State k s a)
stateMonadReturn s a = M.unit (adjunctionMonad (curryAdj s)) ! a

stateMonadJoin :: CartesianClosed k => Obj k s -> Obj k a -> k (State k s (State k s a)) (State k s a)
stateMonadJoin s a = M.multiply (adjunctionMonad (curryAdj s)) ! a

-- ! From every adjunction we also get a comonad, the Context comonad in this case.
type Context k s a = BinaryProduct k (Exponential k s a) s

contextComonadExtract :: CartesianClosed k => Obj k s -> Obj k a -> k (Context k s a) a
contextComonadExtract s a = M.counit (adjunctionComonad (curryAdj s)) ! a

contextComonadDuplicate :: CartesianClosed k => Obj k s -> Obj k a -> k (Context k s a) (Context k s (Context k s a))
contextComonadDuplicate s a = M.comultiply (adjunctionComonad (curryAdj s)) ! a

