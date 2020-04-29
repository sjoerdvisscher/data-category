{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, FlexibleInstances, FlexibleContexts, RankNTypes, ScopedTypeVariables, UndecidableInstances, NoImplicitPrelude  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Kleisli
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

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Monoidal
import qualified Data.Category.Adjunction as A


data Kleisli m a b where
  Kleisli :: (Functor m, Dom m ~ k, Cod m ~ k) => Monad m -> Obj k b -> k a (m :% b) -> Kleisli m a b

kleisliId :: (Functor m, Dom m ~ k, Cod m ~ k) => Monad m -> Obj k a -> Kleisli m a a
kleisliId m a = Kleisli m a (unit m ! a)

-- | The category of Kleisli arrows.
instance Category (Kleisli m) where

  src (Kleisli m _ f) = kleisliId m (src f)
  tgt (Kleisli m b _) = kleisliId m b

  (Kleisli m c f) . (Kleisli _ _ g) = Kleisli m c ((multiply m ! c) . (monadFunctor m % f) . g)



newtype KleisliFree m = KleisliFree (Monad m)
instance (Functor m, Dom m ~ k, Cod m ~ k) => Functor (KleisliFree m) where
  type Dom (KleisliFree m) = Dom m
  type Cod (KleisliFree m) = Kleisli m
  type KleisliFree m :% a = a
  KleisliFree m % f = Kleisli m (tgt f) ((unit m ! tgt f) . f)

data KleisliForget m = KleisliForget
instance (Functor m, Dom m ~ k, Cod m ~ k) => Functor (KleisliForget m) where
  type Dom (KleisliForget m) = Kleisli m
  type Cod (KleisliForget m) = Dom m
  type KleisliForget m :% a = m :% a
  KleisliForget % Kleisli m b f = (multiply m ! b) . (monadFunctor m % f)

kleisliAdj :: (Functor m, Dom m ~ k, Cod m ~ k)
  => Monad m -> A.Adjunction (Kleisli m) k (KleisliFree m) (KleisliForget m)
kleisliAdj m = A.mkAdjunctionInit (KleisliFree m) KleisliForget (unit m !) (\(Kleisli _ x _) f -> Kleisli m x f)
