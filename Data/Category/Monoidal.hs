{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, Rank2Types, ViewPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Monoidal
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Monoidal where

import Prelude (($), uncurry)
import qualified Control.Monad as M
import qualified Data.Monoid as M

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction (Adjunction(Adjunction))
import Data.Category.Limit
import Data.Category.Product

class Functor f => HasUnit f where
  
  type Unit f :: *
  unitObject :: f -> Obj (Cod f) (Unit f)


instance (HasTerminalObject (~>), HasBinaryProducts (~>)) => HasUnit (ProductFunctor (~>)) where
  
  type Unit (ProductFunctor (~>)) = TerminalObject (~>)
  unitObject _ = terminalObject

instance (HasInitialObject (~>), HasBinaryCoproducts (~>)) => HasUnit (CoproductFunctor (~>)) where
  
  type Unit (CoproductFunctor (~>)) = InitialObject (~>)
  unitObject _ = initialObject

instance Category (~>) => HasUnit (FunctorCompose (~>)) where
  
  type Unit (FunctorCompose (~>)) = Id (~>)
  unitObject _ = natId Id
  


class HasUnit f => TensorProduct f where
  
  leftUnitor     :: Cod f ~ (~>) => f -> Obj (~>) a -> (f :% (Unit f, a)) ~> a
  leftUnitorInv  :: Cod f ~ (~>) => f -> Obj (~>) a -> a ~> (f :% (Unit f, a))
  rightUnitor    :: Cod f ~ (~>) => f -> Obj (~>) a -> (f :% (a, Unit f)) ~> a
  rightUnitorInv :: Cod f ~ (~>) => f -> Obj (~>) a -> a ~> (f :% (a, Unit f))
  
  associator     :: Cod f ~ (~>) => f -> Obj (~>) a -> Obj (~>) b -> Obj (~>) c -> (f :% (f :% (a, b), c)) ~> (f :% (a, f :% (b, c)))
  associatorInv  :: Cod f ~ (~>) => f -> Obj (~>) a -> Obj (~>) b -> Obj (~>) c -> (f :% (a, f :% (b, c))) ~> (f :% (f :% (a, b), c))


instance (HasTerminalObject (~>), HasBinaryProducts (~>)) => TensorProduct (ProductFunctor (~>)) where
  
  leftUnitor     _ a = proj2 terminalObject a
  leftUnitorInv  _ a = terminate a &&& a
  rightUnitor    _ a = proj1 a terminalObject
  rightUnitorInv _ a = a &&& terminate a

  associator    _ a b c = (proj1 a b . proj1 (a *** b) c) &&& (proj2 a b *** c)
  associatorInv _ a b c = (a *** proj1 b c) &&& (proj2 b c . proj2 a (b *** c))

instance (HasInitialObject (~>), HasBinaryCoproducts (~>)) => TensorProduct (CoproductFunctor (~>)) where
  
  leftUnitor     _ a = initialize a ||| a
  leftUnitorInv  _ a = inj2 initialObject a
  rightUnitor    _ a = a ||| initialize a
  rightUnitorInv _ a = inj1 a initialObject
  
  associator    _ a b c = (a +++ inj1 b c) ||| (inj2 a (b +++ c) . inj2 b c)
  associatorInv _ a b c = (inj1 (a +++ b) c . inj1 a b) ||| (inj2 a b +++ c)
  
instance Category (~>) => TensorProduct (FunctorCompose (~>)) where
  
  leftUnitor     _ (Nat g _ _) = idPostcomp g
  leftUnitorInv  _ (Nat g _ _) = idPostcompInv g
  rightUnitor    _ (Nat g _ _) = idPrecomp g
  rightUnitorInv _ (Nat g _ _) = idPrecompInv g

  associator    _ (Nat f _ _) (Nat g _ _) (Nat h _ _) = Nat ((f :.: g) :.: h) (f :.: (g :.: h)) $ \i -> f % g % h % i
  associatorInv _ (Nat f _ _) (Nat g _ _) (Nat h _ _) = Nat (f :.: (g :.: h)) ((f :.: g) :.: h) $ \i -> f % g % h % i



data MonoidObject f a = MonoidObject
  { unit     :: (Cod f ~ (~>)) => Unit f        ~> a
  , multiply :: (Cod f ~ (~>)) => (f :% (a, a)) ~> a
  }
  
data ComonoidObject f a = ComonoidObject
  { counit     :: (Cod f ~ (~>)) => a ~> Unit f
  , comultiply :: (Cod f ~ (~>)) => a ~> (f :% (a, a))
  }


preludeMonoid :: M.Monoid m => MonoidObject (ProductFunctor (->)) m
preludeMonoid = MonoidObject M.mempty (uncurry M.mappend)


data MonoidAsCategory f m a b where
  MonoidValue :: (TensorProduct f , Dom f ~ ((~>) :**: (~>)), Cod f ~ (~>))
              => f -> MonoidObject f m -> Unit f ~> m -> MonoidAsCategory f m m m

instance Category (MonoidAsCategory f m) where
  
  src (MonoidValue f m _) = MonoidValue f m $ unit m
  tgt (MonoidValue f m _) = MonoidValue f m $ unit m
  
  MonoidValue f m a . MonoidValue _ _ b = MonoidValue f m $ multiply m . f % (a :**: b) . leftUnitorInv f (unitObject f)



type Monad f = MonoidObject (FunctorCompose (Dom f)) f

mkMonad :: (Functor f, Dom f ~ (~>), Cod f ~ (~>), Category (~>)) 
  => f 
  -> (forall a. Obj (~>) a -> Component (Id (~>)) f a) 
  -> (forall a. Obj (~>) a -> Component (f :.: f) f a)
  -> Monad f
mkMonad f ret join = MonoidObject
  { unit     = Nat Id        f ret
  , multiply = Nat (f :.: f) f join
  }

preludeMonad :: (M.Functor f, M.Monad f) => Monad (EndoHask f)
preludeMonad = mkMonad EndoHask (\_ -> M.return) (\_ -> M.join)

monadFunctor :: forall f. Monad f -> f
monadFunctor (unit -> Nat _ f _) = f


type Comonad f = ComonoidObject (FunctorCompose (Dom f)) f

mkComonad :: (Functor f, Dom f ~ (~>), Cod f ~ (~>), Category (~>)) 
  => f 
  -> (forall a. Obj (~>) a -> Component f (Id (~>)) a) 
  -> (forall a. Obj (~>) a -> Component f (f :.: f) a)
  -> Comonad f
mkComonad f extr dupl = ComonoidObject
  { counit     = Nat f Id        extr
  , comultiply = Nat f (f :.: f) dupl
  }


adjunctionMonad :: Adjunction c d f g -> Monad (g :.: f)
adjunctionMonad (Adjunction f g un coun) = mkMonad (g :.: f) (un !) ((Wrap g f % coun) !)

adjunctionComonad :: Adjunction c d f g -> Comonad (f :.: g)
adjunctionComonad (Adjunction f g un coun) = mkComonad (f :.: g) (coun !) ((Wrap f g % un) !)
