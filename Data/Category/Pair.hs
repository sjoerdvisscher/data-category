{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Pair
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Pair, the category with just 2 objects and their identity arrows.
-- The limit and colimit of the functor from Pair to some category provide 
-- products and coproducts in that category.
-----------------------------------------------------------------------------
module Data.Category.Pair where

import Prelude (($), undefined)

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation


data P1
data P2

-- | The arrows of Pair.
data Pair :: * -> * -> * where
  IdFst :: Pair P1 P1
  IdSnd :: Pair P2 P2

instance Category Pair where
  
  data Obj Pair a where
    Fst :: Obj Pair P1
    Snd :: Obj Pair P2
  
  src IdFst = Fst
  src IdSnd = Snd
  
  tgt IdFst = Fst
  tgt IdSnd = Snd
  
  id  Fst       = IdFst
  id  Snd       = IdSnd
  
  IdFst . IdFst = IdFst
  IdSnd . IdSnd = IdSnd
  _     . _     = undefined -- this can't happen


-- | The functor from Pair to (~>), a diagram of 2 objects in (~>).
data PairDiagram :: (* -> * -> *) -> * -> * -> * where
  PairDiagram :: Category (~>) => Obj (~>) x -> Obj (~>) y -> PairDiagram (~>) x y
type instance Dom (PairDiagram (~>) x y) = Pair
type instance Cod (PairDiagram (~>) x y) = (~>)
type instance PairDiagram (~>) x y :% P1 = x
type instance PairDiagram (~>) x y :% P2 = y
instance Functor (PairDiagram (~>) x y) where
  PairDiagram x _ %% Fst = x
  PairDiagram _ y %% Snd = y
  PairDiagram x _ % IdFst = id x
  PairDiagram _ y % IdSnd = id y


pairNat :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
  => f -> g -> Comp f g P1 -> Comp f g P2 -> Nat Pair d f g
pairNat f g c1 c2 = Nat f g (\x -> unCom $ n c1 c2 x) where
  n :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
    => Comp f g P1 -> Comp f g P2 -> Obj Pair a -> Comp f g a
  n c _ Fst = c
  n _ c Snd = c
