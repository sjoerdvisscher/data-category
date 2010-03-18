{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
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

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Functor

-- | One object of Pair
data Fst = Fst deriving Show
-- | The other object of Pair
data Snd = Snd deriving Show

instance CategoryO Pair Fst where
  id = IdFst
instance CategoryO Pair Snd where
  id = IdSnd

-- | The arrows of Pair.
data family Pair a b :: *
data instance Pair Fst Fst = IdFst
data instance Pair Snd Snd = IdSnd

instance CategoryA Pair Fst Fst Fst where
  IdFst . IdFst = IdFst
instance CategoryA Pair Snd Snd Snd where
  IdSnd . IdSnd = IdSnd

instance Apply Pair Fst Fst where
  IdFst $$ Fst = Fst
instance Apply Pair Snd Snd where
  IdSnd $$ Snd = Snd

  
data instance Funct Pair d f g = 
  (:***:) (Component f g Fst) (Component f g Snd)
instance GetComponent Pair d Fst where
  (f :***: _) ! Fst = f
instance GetComponent Pair d Snd where
  (_ :***: s) ! Snd = s

instance (Dom f ~ Pair, Cod f ~ d, CategoryO d (F f Fst), CategoryO d (F f Snd)) => CategoryO (Funct Pair d) f where
  id = id :***: id
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag Pair (~>)) a b where
  Diag % f = f :***: f

-- | The functor from Pair to (~>), a diagram of 2 objects in (~>).
data PairF ((~>) :: * -> * -> *) x y = PairF
type instance Dom (PairF (~>) x y) = Pair
type instance Cod (PairF (~>) x y) = (~>)
type instance F (PairF (~>) x y) Fst = x
type instance F (PairF (~>) x y) Snd = y
instance (CategoryO (~>) x) => FunctorA (PairF (~>) x y) Fst Fst where
  PairF % IdFst = id
instance (CategoryO (~>) y) => FunctorA (PairF (~>) x y) Snd Snd where
  PairF % IdSnd = id

-- | The product of 2 objects is the limit of the functor from Pair to (~>).
class (CategoryO (~>) x, CategoryO (~>) y) => PairLimit (~>) x y where
  type Product x y :: *
  pairLimit :: Limit (PairF (~>) x y) (Product x y)
  proj1 :: Product x y ~> x
  proj2 :: Product x y ~> y
  proj1 = p where TerminalUniversal (p :***: _) _ = pairLimit :: Limit (PairF (~>) x y) (Product x y)
  proj2 = p where TerminalUniversal (_ :***: p) _ = pairLimit :: Limit (PairF (~>) x y) (Product x y)
-- | The coproduct of 2 objects is the colimit of the functor from Pair to (~>).
class (CategoryO (~>) x, CategoryO (~>) y) => PairColimit (~>) x y where
  type Coproduct x y :: *
  pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  inj1 :: x ~> Coproduct x y
  inj2 :: y ~> Coproduct x y
  inj1 = i where InitialUniversal (i :***: _) _ = pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  inj2 = i where InitialUniversal (_ :***: i) _ = pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  