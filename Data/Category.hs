{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category (
  
  -- * Categories
    CategoryO(..)
  , CategoryA(..)
  , Apply(..)
  , Obj, obj
  
  -- * Functors
  , F
  , Dom
  , Cod
  , FunctorA(..)
  , ContraFunctorA(..)
  
  -- ** Functor instances
  , Id(..)
  , (:.:)(..)
  , Const(..)
  , (:*-:)(..)
  , (:-*:)(..)
  
  -- * Natural transformations
  , Nat
  , (:~>)
  , Component
  
  -- * Universal arrows
  , InitialUniversal(..)
  , TerminalUniversal(..)
  
  -- * Adjunctions
  , Adjunction(..)
  
  ) where

import Prelude hiding ((.), id, ($))


-- | An instance CategoryO (~>) a declares a as an object of the category (~>).
class CategoryO (~>) a where
  id  :: a ~> a
  (!) :: Nat (~>) d f g -> Obj a -> Component f g a

-- | An instance CategoryA (~>) a b c defines composition of the arrows a ~> b and b ~> c.
class (CategoryO (~>) a, CategoryO (~>) b, CategoryO (~>) c) => CategoryA (~>) a b c where
  (.) :: b ~> c -> a ~> b -> a ~> c

class (CategoryO (~>) a, CategoryO (~>) b) => Apply (~>) a b where
  -- Would have liked to use ($) here, but that causes GHC to crash.
  -- http://hackage.haskell.org/trac/ghc/ticket/3297
  ($$) :: a ~> b -> a -> b

-- | The type synonym @Obj a@, when used as the type of a function argument,
-- is a promise that the value of the argument is not used, and only the type.
-- This is used to pass objects (which are types) to functions.
type Obj a = a
-- | 'obj' is a synonym for 'undefined'. When you need to pass an object to
-- a function, you can use @(obj :: type)@.
obj :: Obj a
obj = undefined



-- | Functors are represented by a type tag. The type family 'F' turns the tag into the actual functor.
type family F ftag a :: *
-- | The domain, or source category, of the functor.
type family Dom ftag :: * -> * -> *
-- | The codomain, or target category, of the funcor.
type family Cod ftag :: * -> * -> *

-- | The mapping of arrows by covariant functors.
-- To make this type check, we need to pass the type tag along.
class (CategoryO (Dom ftag) a, CategoryO (Dom ftag) b) 
  => FunctorA ftag a b where
  (%) :: Obj ftag -> Dom ftag a b -> Cod ftag (F ftag a) (F ftag b)

-- | The mapping of arrows by contravariant functors.
class (CategoryO (Dom ftag) a, CategoryO (Dom ftag) b) 
  => ContraFunctorA ftag a b where
  (-%) :: Obj ftag -> Dom ftag a b -> Cod ftag (F ftag b) (F ftag a)


-- | The identity functor on (~>)
data Id ((~>) :: * -> * -> *) = Id
type instance F (Id (~>)) a = a
type instance Dom (Id (~>)) = (~>)
type instance Cod (Id (~>)) = (~>)
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Id (~>)) a b where
  _ % f = f

-- | The composition of two functors.
data (g :.: h) = g :.: h
type instance F (g :.: h) a = F g (F h a)
type instance Dom (g :.: h) = Dom h
type instance Cod (g :.: h) = Cod g
instance (FunctorA g (F h a) (F h b), FunctorA h a b, Cod h ~ Dom g) => FunctorA (g :.: h) a b where
   _ % f = (obj :: g) % ((obj :: h) % f)

-- | The constant functor.
data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x = Const
type instance F (Const c1 c2 x) a = x
type instance Dom (Const c1 c2 x) = c1
type instance Cod (Const c1 c2 x) = c2
instance (CategoryO c1 a, CategoryO c1 b, CategoryO c2 x) => FunctorA (Const c1 c2 x) a b where
  _ % _ = id
  
-- | The covariant functor Hom(X,--)
data (x :*-: ((~>) :: * -> * -> *)) = HomX_
type instance F (x :*-: (~>)) a = x ~> a
type instance Dom (x :*-: (~>)) = (~>)
type instance Cod (x :*-: (~>)) = (->)
instance (CategoryO (~>) a, CategoryO (~>) b, CategoryA (~>) x a b) => FunctorA (x :*-: (~>)) a b where
  _ % f = (f .)

-- | The contravariant functor Hom(--,X)
data (((~>) :: * -> * -> *) :-*: x) = Hom_X
type instance F ((~>) :-*: x) a = a ~> x
type instance Dom ((~>) :-*: x) = (~>)
type instance Cod ((~>) :-*: x) = (->)
instance (CategoryO (~>) a, CategoryO (~>) b, CategoryA (~>) a b x) => ContraFunctorA ((~>) :-*: x) a b where
  _ -% f = (. f)
  
  
data family Nat (c :: * -> * -> *) (d :: * -> * -> *) (f :: *) (g :: *) :: *

-- | @f :~> g@ is a natural transformation from functor f to functor g.
type f :~> g = (c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) => Nat c d f g

-- | Natural transformations are built up of components, 
-- one for each object @z@ in the domain category of @f@ and @g@.
-- This type synonym can be used when creating data instances of @Nat@.
type Component f g z = Cod f (F f z) (F g z)
  
type InitMorF x u = (x :*-: Cod u) :.: u
type TermMorF x u = (Cod u :-*: x) :.: u
data InitialUniversal  x u a = InitialUniversal  (F (InitMorF x u) a) (InitMorF x u :~> (a :*-: Dom u))
data TerminalUniversal x u a = TerminalUniversal (F (TermMorF x u) a) (TermMorF x u :~> (Dom u :-*: a))

data Adjunction f g = Adjunction 
  { unit :: Id (Dom f) :~> (g :.: f)
  , counit :: (f :.: g) :~> Id (Dom g)
  }