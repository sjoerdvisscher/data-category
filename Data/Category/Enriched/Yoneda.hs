{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , RankNTypes
  , PatternSynonyms
  , FlexibleContexts
  , FlexibleInstances
  , NoImplicitPrelude
  , UndecidableInstances
  , ScopedTypeVariables
  , ConstraintKinds
  , MultiParamTypeClasses
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Enriched.Yoneda
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Enriched.Yoneda where

import Data.Kind (Type)

import Data.Category (Category(..), Obj)
import Data.Category.CartesianClosed (CartesianClosed(..), curry)
import Data.Category.Limit (HasBinaryProducts(..), HasTerminalObject(..))
import Data.Category.Enriched
import Data.Category.Enriched.Functor
import Data.Category.Enriched.Limit


yoneda    :: forall f k x. (HasEnds (V k), EFunctorOf k (Self (V k)) f) => f -> Obj k x -> V k (End (V k) (EHomX_ k x :->>: f)) (f :%% x)
yoneda f x = apply (hom x x) (getSelf (f %% x)) . (endCounit (EHomX_ x ->> f) x &&& id x . terminate (end (EHomX_ x ->> f)))

yonedaInv :: forall f k x. (HasEnds (V k), EFunctorOf k (Self (V k)) f) => f -> Obj k x -> V k (f :%% x) (End (V k) (EHomX_ k x :->>: f))
yonedaInv f x = endFactorizer (EHomX_ x ->> f) h
  where
    h :: Obj k a -> V k (f :%% x) (Exponential (V k) (k $ (x, a)) (f :%% a))
    h a = curry fx xa fa (apply fx fa . (map f x a . proj2 fx xa &&& proj1 fx xa))
      where
        xa = hom x a
        Self fx = f %% x
        Self fa = f %% a

data Y (k :: Type -> Type -> Type) = Y
-- | Yoneda embedding
instance (ECategory k, HasEnds (V k)) => EFunctor (Y k) where
  type EDom (Y k) = EOp k
  type ECod (Y k) = FunCat k (Self (V k))
  type Y k :%% x = EHomX_ k x
  Y %% EOp x = FArr (EHomX_ x) (EHomX_ x)
  map Y (EOp a) (EOp b) = yonedaInv (EHomX_ b) a
