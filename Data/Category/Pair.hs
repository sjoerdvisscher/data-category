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
  P1 :: Pair P1 P1
  P2 :: Pair P2 P2

-- | The category with just 2 objects and their identity arrows.
instance Category Pair where
  
  src P1  = P1
  src P2  = P2
  
  tgt P1  = P1
  tgt P2  = P2
  
  P1 . P1 = P1
  P2 . P2 = P2
  _     . _     = undefined -- this can't happen


-- | The functor from Pair to (~>), a diagram of 2 objects in (~>).
data PairDiagram :: (* -> * -> *) -> * -> * -> * where
  PairDiagram :: Category (~>) => Obj (~>) x -> Obj (~>) y -> PairDiagram (~>) x y
type instance Dom (PairDiagram (~>) x y) = Pair
type instance Cod (PairDiagram (~>) x y) = (~>)
type instance PairDiagram (~>) x y :% P1 = x
type instance PairDiagram (~>) x y :% P2 = y
instance Category (~>) => Functor (PairDiagram (~>) x y) where
  PairDiagram x _ % P1 = x
  PairDiagram _ y % P2 = y


pairNat :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
  => f -> g -> Com f g P1 -> Com f g P2 -> Nat Pair d f g
pairNat f g c1 c2 = Nat f g (\x -> unCom $ n c1 c2 x) where
  n :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
    => Com f g P1 -> Com f g P2 -> Obj Pair a -> Com f g a
  n c _ P1 = c
  n _ c P2 = c

arrowPair :: Category (~>) => (x1 ~> x2) -> (y1 ~> y2) -> Nat Pair (~>) (PairDiagram (~>) x1 y1) (PairDiagram (~>) x2 y2)
arrowPair l r = pairNat (PairDiagram (src l) (src r)) (PairDiagram (tgt l) (tgt r)) (Com l) (Com r)
