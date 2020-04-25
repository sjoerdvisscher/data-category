{-# LANGUAGE TypeFamilies, GADTs, TypeOperators, LambdaCase, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Boolean
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- /2/, or the Boolean category.
-- It contains 2 objects, one for true and one for false.
-- It contains 3 arrows, 2 identity arrows and one from false to true.
-----------------------------------------------------------------------------
module Data.Category.Boolean where

import Data.Category
import Data.Category.Limit
import Data.Category.Monoidal
import Data.Category.CartesianClosed

import Data.Category.Functor
import Data.Category.NaturalTransformation


data Fls
data Tru

data Boolean a b where
  Fls :: Boolean Fls Fls
  F2T :: Boolean Fls Tru
  Tru :: Boolean Tru Tru

-- | @Boolean@ is the category with true and false as objects, and an arrow from false to true.
instance Category Boolean where

  src Fls   = Fls
  src F2T   = Fls
  src Tru   = Tru

  tgt Fls   = Fls
  tgt F2T   = Tru
  tgt Tru   = Tru

  Fls . Fls = Fls
  F2T . Fls = F2T
  Tru . F2T = F2T
  Tru . Tru = Tru


-- | False is the initial object in the Boolean category.
instance HasInitialObject Boolean where
  type InitialObject Boolean = Fls
  initialObject = Fls
  initialize Fls = Fls
  initialize Tru = F2T

-- | True is the terminal object in the Boolean category.
instance HasTerminalObject Boolean where
  type TerminalObject Boolean = Tru
  terminalObject = Tru
  terminate Fls = F2T
  terminate Tru = Tru


-- | Conjunction is the binary product in the Boolean category.
instance HasBinaryProducts Boolean where

  type BinaryProduct Boolean Fls Fls = Fls
  type BinaryProduct Boolean Fls Tru = Fls
  type BinaryProduct Boolean Tru Fls = Fls
  type BinaryProduct Boolean Tru Tru = Tru

  proj1 Fls Fls = Fls
  proj1 Fls Tru = Fls
  proj1 Tru Fls = F2T
  proj1 Tru Tru = Tru
  proj2 Fls Fls = Fls
  proj2 Fls Tru = F2T
  proj2 Tru Fls = Fls
  proj2 Tru Tru = Tru

  Fls &&& Fls = Fls
  Fls &&& F2T = Fls
  F2T &&& Fls = Fls
  F2T &&& F2T = F2T
  Tru &&& Tru = Tru


-- | Disjunction is the binary coproduct in the Boolean category.
instance HasBinaryCoproducts Boolean where

  type BinaryCoproduct Boolean Fls Fls = Fls
  type BinaryCoproduct Boolean Fls Tru = Tru
  type BinaryCoproduct Boolean Tru Fls = Tru
  type BinaryCoproduct Boolean Tru Tru = Tru

  inj1 Fls Fls = Fls
  inj1 Fls Tru = F2T
  inj1 Tru Fls = Tru
  inj1 Tru Tru = Tru
  inj2 Fls Fls = Fls
  inj2 Fls Tru = Tru
  inj2 Tru Fls = F2T
  inj2 Tru Tru = Tru

  Fls ||| Fls = Fls
  F2T ||| F2T = F2T
  F2T ||| Tru = Tru
  Tru ||| F2T = Tru
  Tru ||| Tru = Tru


-- | Implication makes the Boolean category cartesian closed.
instance CartesianClosed Boolean where

  type Exponential Boolean Fls Fls = Tru
  type Exponential Boolean Fls Tru = Tru
  type Exponential Boolean Tru Fls = Fls
  type Exponential Boolean Tru Tru = Tru

  apply Fls Fls = Fls
  apply Fls Tru = F2T
  apply Tru Fls = Fls
  apply Tru Tru = Tru

  tuple Fls Fls = F2T
  tuple Fls Tru = Tru
  tuple Tru Fls = Fls
  tuple Tru Tru = Tru

  Fls ^^^ Fls = Tru
  Fls ^^^ F2T = F2T
  Fls ^^^ Tru = Fls
  F2T ^^^ Fls = Tru
  F2T ^^^ F2T = F2T
  F2T ^^^ Tru = F2T
  Tru ^^^ Fls = Tru
  Tru ^^^ F2T = Tru
  Tru ^^^ Tru = Tru


trueProductMonoid :: MonoidObject (ProductFunctor Boolean) Tru
trueProductMonoid = MonoidObject Tru Tru

falseCoproductComonoid :: ComonoidObject (CoproductFunctor Boolean) Fls
falseCoproductComonoid = ComonoidObject Fls Fls

trueProductComonoid :: ComonoidObject (ProductFunctor Boolean) Tru
trueProductComonoid = ComonoidObject Tru Tru

falseCoproductMonoid :: MonoidObject (CoproductFunctor Boolean) Fls
falseCoproductMonoid = MonoidObject Fls Fls

trueCoproductMonoid :: MonoidObject (CoproductFunctor Boolean) Tru
trueCoproductMonoid = MonoidObject F2T Tru

falseProductComonoid :: ComonoidObject (ProductFunctor Boolean) Fls
falseProductComonoid = ComonoidObject F2T Fls


data Arrow k a b = Arrow (k a b)
-- | Any functor from the Boolean category points to an arrow in its target category.
instance Category k => Functor (Arrow k a b) where
  type Dom (Arrow k a b) = Boolean
  type Cod (Arrow k a b) = k
  type Arrow k a b :% Fls = a
  type Arrow k a b :% Tru = b
  Arrow f % Fls = src f
  Arrow f % F2T = f
  Arrow f % Tru = tgt f


type instance LimitFam Boolean k f = f :% Fls
-- | The limit of a functor from the Boolean category is the source of the arrow it points to.
instance Category k => HasLimits Boolean k where
  limit (Nat f _ _) = Nat (Const (f % Fls)) f (\case Fls -> f % Fls; Tru -> f % F2T)
  limitFactorizer n = n ! Fls

type instance ColimitFam Boolean k f = f :% Tru
-- | The colimit of a functor from the Boolean category is the target of the arrow it points to.
instance Category k => HasColimits Boolean k where
  colimit (Nat f _ _) = Nat f (Const (f % Tru)) (\case Fls -> f % F2T; Tru -> f % Tru)
  colimitFactorizer n = n ! Tru
