{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, UndecidableInstances, GADTs, RankNTypes, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.KanExtension
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.KanExtension where

import Prelude (($), undefined)

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit
import Data.Category.Discrete


type family Ran k t :: *

type RanUniversal k t = TerminalUniversal t (Precompose k (Cod t)) (Ran k t)

mkRanUniversal :: (Dom k ~ m, Cod k ~ c, Dom t ~ m, Cod t ~ a, Dom r ~ c, Cod r ~ a, r ~ Ran k t) 
  => Nat m a (r :.: k) t -> (forall s. Obj (Nat c a) s -> Nat m a (s :.: k) t -> Nat c a s r) -> RanUniversal k t
mkRanUniversal eps@(Nat (r :.: _) _ _) f = TerminalUniversal
  { tuObject = natId r
  , terminalMorphism = eps
  , terminalFactorizer = f
  }
  

e :: Const m Unit Z
e = Const Z

type instance Ran (Const m Unit Z) f = Const Unit (Cod f) (Limit f)

rightKanUniversalForLimits :: (Functor f, Category m, Dom f ~ m) => LimitUniversal f -> RanUniversal (Const m Unit Z) f
rightKanUniversalForLimits (TerminalUniversal v n@(Nat _ f _) lf) = mkRanUniversal 
  (Nat (Const v :.: e) f (n !)) undefined
  

type instance Ran (Id m) t = Yoneda t

yonedaToRanUniversal :: forall t m . (Functor t, Category m, Dom t ~ m, Cod t ~ (->)) => t -> RanUniversal (Id m) t
yonedaToRanUniversal t = mkRanUniversal (Nat (Yoneda :.: Id) t (fromYoneda t !)) f
  where
    f :: forall s. Obj (Nat m (->)) s -> Nat m (->) (s :.: Id m) t -> Nat m (->) s (Yoneda t)
    f (Nat s _ _) st = Nat s Yoneda ((toYoneda t . st) !)