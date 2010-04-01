{-# LANGUAGE TypeFamilies, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
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
  
import Prelude hiding ((.), id, Monad(..))

import Data.Category
import Data.Category.Hask

class Pointed m where
  point :: m -> Id (Cod m) :~> m
  
class Pointed m => Monad m where
  join :: m -> (m :.: m) :~> m
  
data Kleisli ((~>) :: * -> * -> *) m a b = Kleisli (m -> a ~> F m b)

newtype instance Nat (Kleisli (~>) m) d f g = 
  KleisliNat { unKleisliNat :: forall a. CategoryO (~>) a => Obj a -> Component f g a }

instance (Monad m, Dom m ~ (~>), Cod m ~ (~>)) => Category (Kleisli (~>) m) where
  idNat = KleisliNat $ \o -> Kleisli $ \m -> point m ! o
instance (Monad m, Dom m ~ (~>), Cod m ~ (~>), CategoryO (~>) o) => CategoryO (Kleisli (~>) m) o where
  (!) = unKleisliNat
instance (Monad m, Dom m ~ (->), Cod m ~ (->), FunctorA m b (F m c)) => CategoryA (Kleisli (->) m) a b c where
  (Kleisli f) . (Kleisli g) = Kleisli $ \m -> join m ! (obj :: c) . (m % f m) . g m



data KleisliAdjF ((~>) :: * -> * -> *) m = KleisliAdjF m
type instance Dom (KleisliAdjF (~>) m) = (~>)
type instance Cod (KleisliAdjF (~>) m) = Kleisli (~>) m
type instance F (KleisliAdjF (~>) m) a = a
instance (Monad m, Dom m ~ (->), Cod m ~ (->)) => FunctorA (KleisliAdjF (->) m) a b where
  KleisliAdjF _ % f = Kleisli $ \m -> point m ! (obj :: b) . f
  
data KleisliAdjG ((~>) :: * -> * -> *) m = KleisliAdjG m
type instance Dom (KleisliAdjG (~>) m) = Kleisli (~>) m
type instance Cod (KleisliAdjG (~>) m) = (~>)
type instance F (KleisliAdjG (~>) m) a = F m a
instance (Monad m, Dom m ~ (->), Cod m ~ (->), FunctorA m a (F m b)) => FunctorA (KleisliAdjG (->) m) a b where
  KleisliAdjG m % Kleisli f = join m ! (obj :: b) . (m % f m)

instance (Pointed m, Dom m ~ (->), Cod m ~ (->)) => Pointed (KleisliAdjG (->) m :.: KleisliAdjF (->) m) where
  point (KleisliAdjG m :.: _) = HaskNat (point m !)
   
kleisliAdj :: (Monad m, Dom m ~ (->), Cod m ~ (->)) => m -> Adjunction (KleisliAdjF (->) m) (KleisliAdjG (->) m)
kleisliAdj m = Adjunction 
  { unit = point (KleisliAdjG m :.: KleisliAdjF m)
  , counit = KleisliNat (\obja -> Kleisli $ \_ -> undefined) }