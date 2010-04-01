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

instance Category Pair where
  idNat = IdFst :***: IdSnd
instance CategoryO Pair Fst where
  (f :***: _) ! Fst = f  
instance CategoryO Pair Snd where
  (_ :***: s) ! Snd = s  

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

  
data instance Nat Pair d f g = Component f g Fst :***: Component f g Snd
instance Category (Nat Pair (~>)) where
  idNat = undefined
instance (Dom f ~ Pair, Cod f ~ (~>), CategoryO (~>) (F f Fst), CategoryO (~>) (F f Snd)) => CategoryO (Nat Pair (~>)) f where
  id = id :***: id
  FunctNat n ! f = n f
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
  
  proj :: (Product x y ~> x, Product x y ~> y)
  (&&&) :: CategoryO (~>) a => (a ~> x) -> (a ~> y) -> (a ~> Product x y)
  
  pairLimit = TerminalUniversal (p1 :***: p2) undefined where
    (p1, p2) = proj :: (Product x y ~> x, Product x y ~> y)
  proj = (n ! Fst, n ! Snd) where 
    TerminalUniversal n _ = pairLimit :: Limit (PairF (~>) x y) (Product x y)
  l &&& r = (n ! (obj :: a)) (l :***: r) where
    TerminalUniversal _ n = pairLimit :: Limit (PairF (~>) x y) (Product x y)
    

-- | The coproduct of 2 objects is the colimit of the functor from Pair to (~>).
class (CategoryO (~>) x, CategoryO (~>) y) => PairColimit (~>) x y where
  
  type Coproduct x y :: *
  pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  
  inj :: (x ~> Coproduct x y, y ~> Coproduct x y)
  (|||) :: CategoryO (~>) a => (x ~> a) -> (y ~> a) -> (Coproduct x y ~> a)
  
  pairColimit = InitialUniversal (i1 :***: i2) undefined where
    (i1, i2) = inj :: (x ~> Coproduct x y, y ~> Coproduct x y)
  inj = (n ! Fst, n ! Snd) where 
    InitialUniversal n _ = pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)
  l ||| r = (n ! (obj :: a)) (l :***: r) where
    InitialUniversal _ n = pairColimit :: Colimit (PairF (~>) x y) (Coproduct x y)

    
-- t :: Nat Pair (~>) f g -> (Product x y ~> Product a b)
-- t (f :***: g) = (f . proj1) &&& (g . proj2)

-- | Functor product
-- data Prod ((~>) :: * -> * -> *) = Prod
-- type instance Dom (Prod (~>)) = Nat Pair (~>)
-- type instance Cod (Prod (~>)) = (~>)
-- type instance F (Prod (~>)) f = Product (F f Fst) (F f Snd)
-- instance (Dom f ~ Pair, Cod f ~ (~>), Dom g ~ Pair, Cod g ~ (~>), F f Fst ~ fx, F f Snd ~ fy, F g Fst ~ gx, F g Snd ~ gy,
--   CategoryO (~>) fx, CategoryO (~>) fy, CategoryO (~>) gx, CategoryO (~>) gy) 
--   => FunctorA (Prod (~>)) f g where
--   Prod % (f :***: g) = (f . proj1) &&& (g . proj2)

-- data f :*: g = f :*: g
-- type instance Dom (f :*: g) = Dom f -- ~ Dom g
-- type instance Cod (f :*: g) = Cod f -- ~ Cod g
-- type instance F (f :*: g) x = Product (F f x) (F g x)
-- -- instance (FunctorA g a1 b1, FunctorA h a2 b2, a ~ Product a1 a2, b ~ Product b1 b2)
-- --   => FunctorA (g :*: h) a b where
-- --   _ % f = ((obj :: g) % f) &&& ((obj :: h) % f)
-- 
-- -- | Functor coproduct
-- data f :+: g = f :+: g
-- type instance Dom (f :+: g) = Dom f -- ~ Dom g
-- type instance Cod (f :+: g) = Cod f -- ~ Cod g
-- type instance F (f :+: g) x = Coproduct (F f x) (F g x)
