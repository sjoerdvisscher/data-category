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
-- Module      :  Data.Category.Enriched.Limit
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Enriched.Limit where

import Data.Kind (Type)

import Data.Category (Category(..), Obj)
import Data.Category.Functor (Functor(..))
import Data.Category.Limit (HasBinaryProducts(..))
import Data.Category.CartesianClosed (CartesianClosed(..), curry, flip)
import qualified Data.Category.WeightedLimit as Hask
import Data.Category.Enriched
import Data.Category.Enriched.Functor

type VProfunctor k l t = EFunctorOf (EOp k :<>: l) (Self (V k)) t

class CartesianClosed v => HasEnds v where
  type End (v :: Type -> Type -> Type) t :: Type
  end :: (VProfunctor k k t, V k ~ v) => t -> Obj v (End v t)
  endCounit :: (VProfunctor k k t, V k ~ v) => t -> Obj k a -> v (End v t) (t :%% (a, a))
  endFactorizer :: (VProfunctor k k t, V k ~ v) => t -> (forall a. Obj k a -> v x (t :%% (a, a))) -> v x (End v t)


newtype HaskEnd t = HaskEnd { getHaskEnd :: forall k a. VProfunctor k k t => t -> Obj k a -> t :%% (a, a) }
instance HasEnds (->) where
  type End (->) t = HaskEnd t
  end _ e = e
  endCounit t a (HaskEnd e) = e t a
  endFactorizer _ e x = HaskEnd (\_ a -> e a x)


data FunCat a b t s where
  FArr :: (EFunctorOf a b t, EFunctorOf a b s) => t -> s -> FunCat a b t s

type t :->>: s = EHom (ECod t) :.: (Opposite t :<*>: s)
(->>) :: (EFunctor t, EFunctor s, ECod t ~ ECod s, V (ECod t) ~ V (ECod s)) => t -> s -> t :->>: s
t ->> s = EHom :.: (Opposite t :<*>: s)
-- | The enriched functor category @[a, b]@
instance (HasEnds (V a), CartesianClosed (V a), V a ~ V b) => ECategory (FunCat a b) where
  type V (FunCat a b) = V a
  type FunCat a b $ (t, s) = End (V a) (t :->>: s)
  hom (FArr t _) (FArr s _) = end (t ->> s)
  id (FArr t _) = endFactorizer (t ->> t) (\a -> id (t %% a))
  comp (FArr t _) (FArr s _) (FArr r _) = endFactorizer (t ->> r)
    (\a -> comp (t %% a) (s %% a) (r %% a) . (endCounit (s ->> r) a *** endCounit (t ->> s) a))


data EndFunctor (k :: Type -> Type -> Type) = EndFunctor
instance (HasEnds (V k), ECategory k) => EFunctor (EndFunctor k) where
  type EDom (EndFunctor k) = FunCat (EOp k :<>: k) (Self (V k))
  type ECod (EndFunctor k) = Self (V k)
  type EndFunctor k :%% t = End (V k) t
  EndFunctor %% (FArr t _) = Self (end t)
  map EndFunctor (FArr f _) (FArr g _) = curry (end (f ->> g)) (end f) (end g) (endFactorizer g (\a ->
    let aa = EOp a :<>: a in apply (getSelf (f %% aa)) (getSelf (g %% aa)) . (endCounit (f ->> g) aa *** endCounit f a)))


-- d :: j -> k, w :: j -> Self (V k)
type family WeigtedLimit (k :: Type -> Type -> Type) w d :: Type
type Lim w d = WeigtedLimit (ECod d) w d

class (HasEnds (V k), EFunctor w, ECod w ~ Self (V k)) => HasLimits k w where
  limitObj :: EFunctorOf (EDom w) k d => w -> d -> Obj k (Lim w d)
  limit    :: EFunctorOf (EDom w) k d => w -> d -> Obj k e -> V k (k $ (e, Lim w d)) (End (V k) (w :->>: (EHomX_ k e :.: d)))
  limitInv :: EFunctorOf (EDom w) k d => w -> d -> Obj k e -> V k (End (V k) (w :->>: (EHomX_ k e :.: d))) (k $ (e, Lim w d))

-- d :: j -> k, w :: EOp j -> Self (V k)
type family WeigtedColimit (k :: Type -> Type -> Type) w d :: Type
type Colim w d = WeigtedColimit (ECod d) w d

class (HasEnds (V k), EFunctor w, ECod w ~ Self (V k)) => HasColimits k w where
  colimitObj :: (EFunctorOf j k d, EOp j ~ EDom w) => w -> d -> Obj k (Colim w d)
  colimit    :: (EFunctorOf j k d, EOp j ~ EDom w) => w -> d -> Obj k e -> V k (k $ (Colim w d, e)) (End (V k) (w :->>: (EHom_X k e :.: Opposite d)))
  colimitInv :: (EFunctorOf j k d, EOp j ~ EDom w) => w -> d -> Obj k e -> V k (End (V k) (w :->>: (EHom_X k e :.: Opposite d))) (k $ (Colim w d, e))


type instance WeigtedLimit (Self v) w d = End v (w :->>: d)
instance (HasEnds v, EFunctor w, ECod w ~ Self v) => HasLimits (Self v) w where
  limitObj w d = Self (end (w ->> d))
  limit    w d (Self e) = let wed = w ->> (EHomX_ (Self e) :.: d) in endFactorizer wed
    (\a -> let { Self wa = w %% a; Self da = d %% a } in flip e wa da . (endCounit (w ->> d) a ^^^ e))
  limitInv w d (Self e) = let wed = w ->> (EHomX_ (Self e) :.: d) in curry (end wed) e (end (w ->> d))
    (endFactorizer (w ->> d) (\a -> let { Self wa = w %% a; Self da = d %% a } in apply e (da ^^^ wa) . (flip wa e da . endCounit wed a *** e)))

type instance WeigtedLimit (InHask k) (InHaskToHask w) d = Hask.WeightedLimit k w (UnderlyingHask (Dom w) k d)
instance Hask.HasWLimits k w => HasLimits (InHask k) (InHaskToHask w) where
  limitObj (InHaskToHask w) d = InHask (Hask.limitObj w (UnderlyingHask d))
  limit    (InHaskToHask w) d _ el = HaskEnd (\_ (InHask a) wa -> Hask.limit w (UnderlyingHask d) a wa . el)
  limitInv (InHaskToHask w) d (InHask e) (HaskEnd n) =
    Hask.limitFactorizer w (UnderlyingHask d) e (n (InHaskToHask w ->> (EHomX_ (InHask e) :.: d)) . InHask)
