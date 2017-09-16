{-# LANGUAGE
  TypeOperators,
  TypeFamilies,
  GADTs,
  Rank2Types,
  ScopedTypeVariables,
  UndecidableInstances,
  TypeSynonymInstances,
  FlexibleInstances,
  NoImplicitPrelude #-}
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
import Data.Category.Yoneda


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



-- | Exponentials in @Cat@ are the functor categories.
instance CartesianClosed Cat where
  type Exponential Cat (CatW c) (CatW d) = CatW (Nat c d)

  apply CatA{} CatA{}   = CatA Apply
  tuple CatA{} CatA{}   = CatA Tuple
  (CatA f) ^^^ (CatA h) = CatA (Wrap f h)


type PShExponential k y z = (Presheaves k :-*: z) :.: Opposite
  (   ProductFunctor (Presheaves k)
  :.: Tuple2 (Presheaves k) (Presheaves k) y
  :.: YonedaEmbedding k
  )
pshExponential :: Category k => Obj (Presheaves k) y -> Obj (Presheaves k) z -> PShExponential k y z
pshExponential y z = hom_X z :.: Opposite (ProductFunctor :.: tuple2 y :.: yonedaEmbedding)

-- | The category of presheaves on a category @C@ is cartesian closed for any @C@.
instance Category k => CartesianClosed (Presheaves k) where
  type Exponential (Presheaves k) y z = PShExponential k y z

  apply yn@(Nat y _ _) zn@(Nat z _ _) = Nat (pshExponential yn zn :*: y) z (\(Op i) (n, yi) -> (n ! Op i) (i, yi))
  tuple yn zn@(Nat z _ _) = Nat z (pshExponential yn (zn *** yn)) (\(Op i) zi -> (Nat (hom_X i) z (\_ j2i -> (z % Op j2i) zi) *** yn))
  zn ^^^ yn = Nat (pshExponential (tgt yn) (src zn)) (pshExponential (src yn) (tgt zn)) (\(Op i) n -> zn . n . (natId (hom_X i) *** yn))



-- | The product functor is left adjoint the the exponential functor.
curryAdj :: CartesianClosed k
         => Obj k y
         -> Adjunction k k
              (ProductFunctor k :.: Tuple2 k k y)
              (ExpFunctor k :.: Tuple1 (Op k) k y)
curryAdj y = mkAdjunction (ProductFunctor :.: tuple2 y) (ExpFunctor :.: tuple1 (Op y)) (tuple y) (apply y)

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
