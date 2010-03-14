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
-- But the typing issues with natural transformations in Hask make this problematic.
-----------------------------------------------------------------------------
module Data.Category.Kleisli where
  
import Prelude hiding ((.), id, Monad(..))
-- Getting desperate
import Unsafe.Coerce

import Data.Category
import Data.Category.Functor
import Data.Category.Hask

class Pointed m where
  point :: m -> Id (Cod m) :~> m
  
class Pointed m => Monad m where
  join :: m -> (m :.: m) :~> m
  
data Kleisli ((~>) :: * -> * -> *) m a b = Kleisli (m -> a ~> F m b)

instance (Monad m, Dom m ~ (->), Cod m ~ (->)) => CategoryO (Kleisli (->) m) o where
  id = Kleisli $ \m -> unHaskNat (point m)
instance (Monad m, Dom m ~ (->), Cod m ~ (->), FunctorA m b (F m c)) => CategoryA (Kleisli (->) m) a b c where
  (Kleisli f) . (Kleisli g) = Kleisli $ \m -> unsafeCoerce (unHaskNat (join m)) . (m % f m) . g m
newtype instance Funct (Kleisli (->) m) d (FunctO (Kleisli (->) m) d f) (FunctO (Kleisli (->) m) d g) = 
  KleisliNat { unKleisliNat :: (forall a. CategoryO d (F f a) => Component f g a) }

data KleisliAdjF ((~>) :: * -> * -> *) m = KleisliAdjF m
type instance Dom (KleisliAdjF (~>) m) = (~>)
type instance Cod (KleisliAdjF (~>) m) = Kleisli (~>) m
type instance F (KleisliAdjF (~>) m) a = a
instance (Monad m, Dom m ~ (->), Cod m ~ (->)) => FunctorA (KleisliAdjF (->) m) a b where
  KleisliAdjF _ % f = Kleisli $ \m -> unHaskNat (point m) . f
  
data KleisliAdjG ((~>) :: * -> * -> *) m = KleisliAdjG m
type instance Dom (KleisliAdjG (~>) m) = Kleisli (~>) m
type instance Cod (KleisliAdjG (~>) m) = (~>)
type instance F (KleisliAdjG (~>) m) a = F m a
instance (Monad m, Dom m ~ (->), Cod m ~ (->), FunctorA m a (F m b)) => FunctorA (KleisliAdjG (->) m) a b where
  KleisliAdjG m % Kleisli f = unsafeCoerce (unHaskNat (join m)) . (m % f m)

instance (Pointed m, Dom m ~ (->), Cod m ~ (->)) => Pointed (KleisliAdjG (->) m :.: KleisliAdjF (->) m) where
  point (KleisliAdjG m :.: _) = HaskNat (unHaskNat (point m))
   
kleisliAdj :: (Monad m, Dom m ~ (->), Cod m ~ (->)) => m -> Adjunction (KleisliAdjF (->) m) (KleisliAdjG (->) m)
kleisliAdj m = Adjunction { unit = point (KleisliAdjG m :.: KleisliAdjF m), counit = KleisliNat (Kleisli $ \m -> undefined) }