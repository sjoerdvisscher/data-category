{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts, ViewPatterns, ScopedTypeVariables, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Dialg
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Dialg(F,G), the category of (F,G)-dialgebras and (F,G)-homomorphisms.
-----------------------------------------------------------------------------
module Data.Category.Dialg where

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit
import Data.Category.Product
import Data.Category.Monoidal
import qualified Data.Category.Adjunction as A


-- | Objects of Dialg(F,G) are (F,G)-dialgebras.
data Dialgebra f g a where
  Dialgebra :: (Category c, Category d, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Functor f, Functor g)
    => Obj c a -> d (f :% a) (g :% a) -> Dialgebra f g a

-- | Arrows of Dialg(F,G) are (F,G)-homomorphisms.
data Dialg f g a b where
  DialgA :: (Category c, Category d, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Functor f, Functor g)
    => Dialgebra f g a -> Dialgebra f g b -> c a b -> Dialg f g a b

dialgId :: Dialgebra f g a -> Obj (Dialg f g) a
dialgId d@(Dialgebra a _) = DialgA d d a

dialgebra :: Obj (Dialg f g) a -> Dialgebra f g a
dialgebra (DialgA d _ _) = d

-- | The category of (F,G)-dialgebras.
instance Category (Dialg f g) where

  src (DialgA s _ _) = dialgId s
  tgt (DialgA _ t _) = dialgId t

  DialgA _ t f . DialgA s _ g = DialgA s t (f . g)



type Alg f = Dialg f (Id (Dom f))
type Algebra f a = Dialgebra f (Id (Dom f)) a
type Coalg f = Dialg (Id (Dom f)) f
type Coalgebra f a = Dialgebra (Id (Dom f)) f a

-- | The initial F-algebra is the initial object in the category of F-algebras.
type InitialFAlgebra f = InitialObject (Alg f)

-- | The terminal F-coalgebra is the terminal object in the category of F-coalgebras.
type TerminalFAlgebra f = TerminalObject (Coalg f)

-- | A catamorphism of an F-algebra is the arrow to it from the initial F-algebra.
type Cata f a = Algebra f a -> Alg f (InitialFAlgebra f) a

-- | A anamorphism of an F-coalgebra is the arrow from it to the terminal F-coalgebra.
type Ana f a = Coalgebra f a -> Coalg f a (TerminalFAlgebra f)





data NatNum = Z () | S NatNum
primRec :: (() -> t) -> (t -> t) -> NatNum -> t
primRec z _ (Z ()) = z ()
primRec z s (S  n) = s (primRec z s n)

-- | The category for defining the natural numbers and primitive recursion can be described as
-- @Dialg(F,G)@, with @F(A)=\<1,A>@ and @G(A)=\<A,A>@.
instance HasInitialObject (Dialg (Tuple1 (->) (->) ()) (DiagProd (->))) where

  type InitialObject (Dialg (Tuple1 (->) (->) ()) (DiagProd (->))) = NatNum

  initialObject = dialgId (Dialgebra (\x -> x) (Z :**: S))

  initialize (dialgebra -> d@(Dialgebra _ (z :**: s))) = DialgA (dialgebra initialObject) d (primRec z s)



data FreeAlg m = FreeAlg (Monad m)
-- | @FreeAlg@ M takes @x@ to the free algebra @(M x, mu_x)@ of the monad @M@.
instance (Functor m, Dom m ~ k, Cod m ~ k) => Functor (FreeAlg m) where
  type Dom (FreeAlg m) = Dom m
  type Cod (FreeAlg m) = Alg m
  type FreeAlg m :% a = m :% a
  FreeAlg m % f = DialgA (freeAlg m (src f)) (freeAlg m (tgt f)) (monadFunctor m % f)

freeAlg :: (Functor m, Dom m ~ k, Cod m ~ k) => Monad m -> Obj (Cod m) x -> Algebra m (m :% x)
freeAlg m x = Dialgebra (monadFunctor m % x) (multiply m ! x)

data ForgetAlg m = ForgetAlg
-- | @ForgetAlg m@ is the forgetful functor for @Alg m@.
instance (Functor m, Dom m ~ k, Cod m ~ k) => Functor (ForgetAlg m) where
  type Dom (ForgetAlg m) = Alg m
  type Cod (ForgetAlg m) = Dom m
  type ForgetAlg m :% a = a
  ForgetAlg % DialgA _ _ f = f

eilenbergMooreAdj :: (Functor m, Dom m ~ k, Cod m ~ k)
  => Monad m -> A.Adjunction (Alg m) k (FreeAlg m) (ForgetAlg m)
eilenbergMooreAdj m = A.mkAdjunctionUnits (FreeAlg m) ForgetAlg
  (unit m !)
  (\(DialgA b@(Dialgebra _ h) _ _) -> DialgA (Dialgebra (src h) (monadFunctor m % h)) b h)
