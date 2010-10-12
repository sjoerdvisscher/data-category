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
import Data.Category.Monoidal
import qualified Data.Category.Adjunction as A


data Kleisli ((~>) :: * -> * -> *) m a b where
  Kleisli :: Monad m -> Obj (~>) b -> a ~> (m :% b) -> Kleisli (~>) m a b

kleisliId :: (Category (~>), Functor m, Dom m ~ (~>), Cod m ~ (~>)) 
  => Monad m -> Obj (~>) a -> Kleisli (~>) m a a
kleisliId m a = Kleisli m a $ unit m ! a

instance (Category (~>), Functor m, Dom m ~ (~>), Cod m ~ (~>)) => Category (Kleisli (~>) m) where
  
  src (Kleisli m _ f) = kleisliId m (src f)
  tgt (Kleisli m b _) = kleisliId m b
  
  (Kleisli m c f) . (Kleisli _ _ g) = Kleisli m c $ (multiply m ! c) . (monadFunctor m % f) . g



data KleisliAdjF ((~>) :: * -> * -> *) m where
  KleisliAdjF :: Monad m -> KleisliAdjF (~>) m
type instance Dom (KleisliAdjF (~>) m) = (~>)
type instance Cod (KleisliAdjF (~>) m) = Kleisli (~>) m
type instance KleisliAdjF (~>) m :% a = a
instance (Category (~>), Functor m, Dom m ~ (~>), Cod m ~ (~>)) => Functor (KleisliAdjF (~>) m) where
  KleisliAdjF m % f = Kleisli m (tgt f) $ (unit m ! tgt f) . f
   
data KleisliAdjG ((~>) :: * -> * -> *) m where
  KleisliAdjG :: Monad m -> KleisliAdjG (~>) m
type instance Dom (KleisliAdjG (~>) m) = Kleisli (~>) m
type instance Cod (KleisliAdjG (~>) m) = (~>)
type instance KleisliAdjG (~>) m :% a = m :% a
instance (Category (~>), Functor m, Dom m ~ (~>), Cod m ~ (~>)) => Functor (KleisliAdjG (~>) m) where
  KleisliAdjG m % Kleisli _ b f = (multiply m ! b) . (monadFunctor m % f)

kleisliAdj :: (Functor m, Dom m ~ (~>), Cod m ~ (~>), Category (~>)) 
  => Monad m -> A.Adjunction (Kleisli (~>) m) (~>) (KleisliAdjF (~>) m) (KleisliAdjG (~>) m)
kleisliAdj m = A.mkAdjunction (KleisliAdjF m) (KleisliAdjG m)
  (\x -> unit m ! x)
  (\(Kleisli _ x _) -> Kleisli m x $ monadFunctor m % x)
