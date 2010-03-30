{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, UndecidableInstances, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Dialg
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Dialg(F,G), the category of (F,G)-dialgebras and (F,G)-homomorphisms.
-----------------------------------------------------------------------------
module Data.Category.Dialg where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Void

-- | Objects of Dialg(F,G) are (F,G)-dialgebras.
newtype Dialgebra f g a = Dialgebra (Dom f (F f a) (F g a))

-- | Arrows of Dialg(F,G) are (F,G)-homomorphisms.
data family Dialg f g a b :: *
data instance Dialg f g (Dialgebra f g a) (Dialgebra f g b) = DialgA (Dom f a b)

newtype instance Nat (Dialg f g) d s t = 
  DialgNat { unDialgNat :: forall a. Obj (Dialgebra f g a) -> Component s t (Dialgebra f g a) }

instance (Dom f ~ (~>), Cod f ~ (~>), Dom g ~ (~>), Cod g ~ (~>), CategoryO (~>) a) 
  => CategoryO (Dialg f g) (Dialgebra f g a) where
  id = DialgA id
  (!) = unDialgNat
instance (Dom f ~ (~>), Cod f ~ (~>), Dom g ~ (~>), Cod g ~ (~>), CategoryA (~>) a b c) 
  => CategoryA (Dialg f g) (Dialgebra f g a) (Dialgebra f g b) (Dialgebra f g c) where
  DialgA f . DialgA g = DialgA (f . g)

type Alg f = Dialg f (Id (Dom f))
type Algebra f a = Dialgebra f (Id (Dom f)) a
type Coalg f = Dialg (Id (Dom f)) f
type Coalgebra f a = Dialgebra (Id (Dom f)) f a

-- | The initial F-algebra is the initial object in the category of F-algebras.
type InitialFAlgebra f = InitialObject (Alg f)

-- | The terminal F-coalgebra is the terminal object in the category of F-coalgebras.
type TerminalFAlgebra f = TerminalObject (Coalg f)

-- | A catamorphism of an F-algebra is the arrow to it from the initial F-algebra.
type Cata f a = Algebra f a -> Alg f (InitialFAlgebra f) (Algebra f a)

-- | A anamorphism of an F-coalgebra is the arrow from it to the terminal F-coalgebra.
type Ana f a = Coalgebra f a -> Coalg f (Coalgebra f a) (TerminalFAlgebra f)
