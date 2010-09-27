{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Void
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Monoidal where

import Prelude hiding ((.), Functor)
import qualified Control.Monad as M

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit


class Functor f => HasUnit f where
  
  type Unit f :: *
  unit :: Obj (Cod f) (Unit f)


instance (HasTerminalObject (~>), HasBinaryProducts (~>)) => HasUnit (ProductFunctor (~>)) where
  
  type Unit (ProductFunctor (~>)) = TerminalObject (~>)
  unit = terminalObject

instance (HasInitialObject (~>), HasBinaryCoproducts (~>)) => HasUnit (CoproductFunctor (~>)) where
  
  type Unit (CoproductFunctor (~>)) = InitialObject (~>)
  unit = initialObject

instance Category (~>) => HasUnit (FunctorCompose (~>)) where
  
  type Unit (FunctorCompose (~>)) = Id (~>)
  unit = natId Id
  


class HasUnit f => TensorProduct f where
  
  leftUnitor     :: Cod f ~ (~>) => Obj (Cod f) a -> (f :% (Unit f, a)) ~> a
  leftUnitorInv  :: Cod f ~ (~>) => Obj (Cod f) a -> a ~> (f :% (Unit f, a))
  
  rightUnitor    :: Cod f ~ (~>) => Obj (Cod f) a -> (f :% (a, Unit f)) ~> a
  rightUnitorInv :: Cod f ~ (~>) => Obj (Cod f) a -> a ~> (f :% (a, Unit f))
  
  associator     :: Cod f ~ (~>) => Obj (Cod f) a -> Obj (Cod f) b -> Obj (Cod f) c -> (f :% (f :% (a, b), c)) ~> (f :% (a, f :% (b, c)))
  associatorInv  :: Cod f ~ (~>) => Obj (Cod f) a -> Obj (Cod f) b -> Obj (Cod f) c -> (f :% (a, f :% (b, c))) ~> (f :% (f :% (a, b), c))


instance (HasTerminalObject (~>), HasBinaryProducts (~>)) => TensorProduct (ProductFunctor (~>)) where
  
  leftUnitor a        = proj2 terminalObject a
  leftUnitorInv a     = terminate a &&& a
  
  rightUnitor a       = proj1 a terminalObject
  rightUnitorInv a    = a &&& terminate a

  associator a b c    = (proj1 a b . proj1 (a *** b) c) &&& (proj2 a b *** c)
  associatorInv a b c = (a *** proj1 b c) &&& (proj2 b c . proj2 a (b *** c))

instance (HasInitialObject (~>), HasBinaryCoproducts (~>)) => TensorProduct (CoproductFunctor (~>)) where
  
  leftUnitor    a = initialize a ||| a
  leftUnitorInv a = inj2 initialObject a
  
  rightUnitor    a = a ||| initialize a
  rightUnitorInv a = inj1 a initialObject
  
  associator    a b c = (a +++ inj1 b c) ||| (inj2 a (b +++ c) . inj2 b c)
  associatorInv a b c = (inj1 (a +++ b) c . inj1 a b) ||| (inj2 a b +++ c)
  
instance Category (~>) => TensorProduct (FunctorCompose (~>)) where
  
  leftUnitor     (Nat g _ _) = Nat (Id :.: g) g $ \i -> g % i
  leftUnitorInv  (Nat g _ _) = Nat g (Id :.: g) $ \i -> g % i

  rightUnitor    (Nat g _ _) = Nat (g :.: Id) g $ \i -> g % i
  rightUnitorInv (Nat g _ _) = Nat g (g :.: Id) $ \i -> g % i

  associator    (Nat f _ _) (Nat g _ _) (Nat h _ _) = Nat ((f :.: g) :.: h) (f :.: (g :.: h)) $ \i -> f % g % h % i
  associatorInv (Nat f _ _) (Nat g _ _) (Nat h _ _) = Nat (f :.: (g :.: h)) ((f :.: g) :.: h) $ \i -> f % g % h % i



data MonoidObject f a = MonoidObject
  { point    :: (Cod f ~ (~>)) => Unit f        ~> a  
  , multiply :: (Cod f ~ (~>)) => (f :% (a, a)) ~> a
  }

preludeMonad :: (M.Functor f, M.Monad f) => MonoidObject (FunctorCompose (->)) (EndoHask f)
preludeMonad = MonoidObject
  { point    = Nat Id                      EndoHask $ \_ -> M.return
  , multiply = Nat (EndoHask :.: EndoHask) EndoHask $ \_ -> M.join
  }  
