{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, UndecidableInstances, GADTs, RankNTypes, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.KanExtension
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.KanExtension where

import Prelude (($))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.RepresentableFunctor
import Data.Category.Limit
import Data.Category.Discrete
import Data.Category.Yoneda


type family Ran k t :: *

type RanUniversal k t = TerminalUniversal t (Precompose k (Cod t)) (Ran k t)

mkRanUniversal :: (Dom k ~ m, Cod k ~ c, Dom t ~ m, Cod t ~ a, Dom r ~ c, Cod r ~ a, r ~ Ran k t) 
  => Nat m a (r :.: k) t -> (forall s. Obj (Nat c a) s -> Nat m a (s :.: k) t -> Nat c a s r) -> RanUniversal k t
mkRanUniversal eps@(Nat (r :.: k) _ _) f = terminalUniversal (Precompose k) (natId r) eps f
  

e :: Const m Unit Z
e = Const Z

type instance Ran (Const m Unit Z) f = Const Unit (Cod f) (Limit f)

rightKanUniversalForLimits :: (HasLimits j (~>), Functor f, Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> RanUniversal (Const j Unit Z) f
rightKanUniversalForLimits f = mkRanUniversal 
    (limit f . constPostcomp (Const v) e)
    (\(Nat s _ _) n -> Nat s (Const v) $ \Z -> limitFactorizer f (n . constPrecompInv e s))
  where
    v = coneVertex (limit f)


type instance Ran (Id m) t = Yoneda t

yonedaToRanUniversal :: forall t m. (Functor t, Category m, Dom t ~ m, Cod t ~ (->)) => t -> RanUniversal (Id m) t
yonedaToRanUniversal t = mkRanUniversal 
    (fromYoneda t . idPrecomp Yoneda)
    (\(Nat s _ _) st -> toYoneda t . st . idPrecompInv s)