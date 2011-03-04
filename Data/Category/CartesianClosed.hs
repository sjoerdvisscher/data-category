{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, Rank2Types, ScopedTypeVariables, UndecidableInstances, TypeSynonymInstances #-}
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
  
import Prelude (($))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Product
import Data.Category.Limit
import Data.Category.Adjunction
import Data.Category.Monoidal as M


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

instance CartesianClosed (->) where
  
  apply _ _ (f, y) = f y
  tuple _ _ z      = \y -> (z, y)
  f ^^^ h          = \g -> f . g . h



data CatApply (y :: * -> * -> *) (z :: * -> * -> *) = CatApply
type instance Dom (CatApply y z) = Nat y z :**: y
type instance Cod (CatApply y z) = z
type instance CatApply y z :% (f, a) = f :% a
instance (Category y, Category z) => Functor (CatApply y z) where
  CatApply % (l :**: r) = l ! r

data CatTuple (y :: * -> * -> *) (z :: * -> * -> *) = CatTuple
type instance Dom (CatTuple y z) = z
type instance Cod (CatTuple y z) = Nat y (z :**: y)
type instance CatTuple y z :% a = Tuple1 z y a
instance (Category y, Category z) => Functor (CatTuple y z) where
  CatTuple % f = Nat (Tuple1 (src f)) (Tuple1 (tgt f)) $ \z -> f :**: z


type instance Exponential Cat (CatW c) (CatW d) = CatW (Nat c d)

instance CartesianClosed Cat where
  
  apply CatA{} CatA{}   = CatA CatApply
  tuple CatA{} CatA{}   = CatA CatTuple
  (CatA f) ^^^ (CatA h) = CatA (Wrap f h)


type Presheaves (~>) = Nat (Op (~>)) (->)

data PShExponential ((~>) :: * -> * -> *) p q = PShExponential
type instance Dom (PShExponential (~>) p q) = Op (~>)
type instance Cod (PShExponential (~>) p q) = (->)
type instance PShExponential (~>) p q :% a = Presheaves (~>) (((~>) :-*: a) :*: p) q
instance (Category (~>), Dom p ~ Op (~>), Dom q ~ Op (~>), Cod p ~ (->), Cod q ~ (->), Functor p, Functor q)
  => Functor (PShExponential (~>) p q) where
  PShExponential % Op f = \(Nat (_ :*: p) q n) -> Nat (hom_X (src f) :*: p) q $ \i (i2a, pi) -> n i (f . i2a, pi)

type instance Exponential (Presheaves (~>)) y z = PShExponential (~>) y z

instance Category (~>) => CartesianClosed (Presheaves (~>)) where
  
  apply (Nat y _ _) (Nat z _ _) = Nat (PShExponential :*: y) z $ \(Op i) (n, yi) -> (n ! Op i) (i, yi)
  tuple (Nat y _ _) (Nat z _ _) = Nat z PShExponential $ \(Op i) zi -> (Nat (hom_X i) z $ \_ j2i -> (z % Op j2i) zi) *** natId y
  zn@Nat{} ^^^ yn@Nat{} = Nat PShExponential PShExponential $ \(Op i) n -> zn . n . (natId (hom_X i) *** yn)

    
curryAdj :: CartesianClosed (~>) 
         => Obj (~>) y 
         -> Adjunction (~>) (~>) 
              (ProductFunctor (~>) :.: Tuple2 (~>) (~>) y) 
              (ExpFunctor (~>) :.: Tuple1 (Op (~>)) (~>) y)
curryAdj y = mkAdjunction (ProductFunctor :.: Tuple2 y) (ExpFunctor :.: Tuple1 (Op y)) (tuple y) (apply y)

curry :: CartesianClosed (~>) => Obj (~>) x -> Obj (~>) y -> Obj (~>) z -> BinaryProduct (~>) x y ~> z -> x ~> Exponential (~>) y z
curry x y _ = leftAdjunct (curryAdj y) x

uncurry :: CartesianClosed (~>) => Obj (~>) x -> Obj (~>) y -> Obj (~>) z -> x ~> Exponential (~>) y z -> BinaryProduct (~>) x y ~> z
uncurry _ y z = rightAdjunct (curryAdj y) z

type State (~>) s a = Exponential (~>) s (BinaryProduct (~>) a s)

stateMonadReturn :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> a ~> State (~>) s a
stateMonadReturn s a = M.unit (adjunctionMonad $ curryAdj s) ! a

stateMonadJoin :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> State (~>) s (State (~>) s a) ~> State (~>) s a
stateMonadJoin s a = M.multiply (adjunctionMonad $ curryAdj s) ! a

type Context (~>) s a = BinaryProduct (~>) (Exponential (~>) s a) s

contextComonadExtract :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> Context (~>) s a ~> a
contextComonadExtract s a = M.counit (adjunctionComonad $ curryAdj s) ! a

contextComonadDuplicate :: CartesianClosed (~>) => Obj (~>) s -> Obj (~>) a -> Context (~>) s a ~> Context (~>) s (Context (~>) s a)
contextComonadDuplicate s a = M.comultiply (adjunctionComonad $ curryAdj s) ! a

