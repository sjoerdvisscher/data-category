{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, FlexibleInstances, FlexibleContexts, RankNTypes, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Kleisli
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This is an attempt at the Kleisli category, and the construction 
-- of an adjunction for each monad.
-----------------------------------------------------------------------------
module Data.Category.Kleisli where
  
import Prelude hiding ((.), id, Functor(..), Monad(..))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction


class Functor m => Pointed m where
  point :: m -> Id (Dom m) :~> m
  
class Pointed m => Monad m where
  join :: m -> (m :.: m) :~> m

  
data Kleisli ((~>) :: * -> * -> *) m a b where
  Kleisli :: m -> Obj (~>) b -> a ~> F m b -> Kleisli (~>) m a b


instance (Category (~>), Monad m, Dom m ~ (~>), Cod m ~ (~>)) => Category (Kleisli (~>) m) where
  
  data Obj (Kleisli (~>) m) a = KleisliO m (Obj (~>) a)
  
  src (Kleisli m _ f) = KleisliO m (src f)
  tgt (Kleisli m b _) = KleisliO m b
  
  id (KleisliO m o)                 = Kleisli m o $ point m ! o
  (Kleisli m c f) . (Kleisli _ _ g) = Kleisli m c $ (join m ! c) . (m % f) . g



data KleisliAdjF ((~>) :: * -> * -> *) m where
  KleisliAdjF :: (Category (~>), Monad m, Dom m ~ (~>), Cod m ~ (~>)) => m -> KleisliAdjF (~>) m
type instance Dom (KleisliAdjF (~>) m) = (~>)
type instance Cod (KleisliAdjF (~>) m) = Kleisli (~>) m
type instance F (KleisliAdjF (~>) m) a = a
instance Functor (KleisliAdjF (~>) m) where
  KleisliAdjF m %% x = KleisliO m x
  KleisliAdjF m %  f = Kleisli m (tgt f) $ (point m ! tgt f) . f
   
data KleisliAdjG ((~>) :: * -> * -> *) m where
  KleisliAdjG :: (Category (~>), Monad m, Dom m ~ (~>), Cod m ~ (~>)) => m -> KleisliAdjG (~>) m
type instance Dom (KleisliAdjG (~>) m) = Kleisli (~>) m
type instance Cod (KleisliAdjG (~>) m) = (~>)
type instance F (KleisliAdjG (~>) m) a = F m a
instance Functor (KleisliAdjG (~>) m) where
  KleisliAdjG m %% KleisliO _ x = m %% x
  KleisliAdjG m % Kleisli _ b f = (join m ! b) . (m % f)

kleisliAdj :: (Monad m, Dom m ~ (~>), Cod m ~ (~>), Category (~>)) 
  => m -> Adjunction (Kleisli (~>) m) (~>) (KleisliAdjF (~>) m) (KleisliAdjG (~>) m)
kleisliAdj m = Adjunction (KleisliAdjF m) (KleisliAdjG m)
  (Nat Id (KleisliAdjG m :.: KleisliAdjF m) $ \x -> point m ! x)
  (Nat (KleisliAdjF m :.: KleisliAdjG m) Id $ \(KleisliO _ x) -> Kleisli m x $ m % id x)
