{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes #-}
module Data.Category where

import Prelude hiding ((.), id, ($))



class CategoryO (~>) a where
  id :: a ~> a
  
class (CategoryO (~>) a, CategoryO (~>) b, CategoryO (~>) c) => CategoryA (~>) a b c where
  (.) :: b ~> c -> a ~> b -> a ~> c

class (CategoryO (~>) a, CategoryO (~>) b) => Apply (~>) a b where
  -- Would have liked to use ($) here, but that causes GHC to crash.
  -- http://hackage.haskell.org/trac/ghc/ticket/3297
  ($$) :: a ~> b -> a -> b
  

type family F ftag a :: *
type family Dom ftag :: * -> * -> *
type family Cod ftag :: * -> * -> *

class (CategoryO (Dom ftag) a, CategoryO (Dom ftag) b) 
  => FunctorA ftag a b where
  (%) :: ftag -> Dom ftag a b -> Cod ftag (F ftag a) (F ftag b)

class (CategoryO (Dom ftag) a, CategoryO (Dom ftag) b) 
  => ContraFunctorA ftag a b where
  (-%) :: ftag -> Dom ftag a b -> Cod ftag (F ftag b) (F ftag a)


-- |The identity functor on (~>)
data Id ((~>) :: * -> * -> *) = Id
type instance F (Id (~>)) a = a
type instance Dom (Id (~>)) = (~>)
type instance Cod (Id (~>)) = (~>)
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Id (~>)) a b where
  Id % f = f

-- |The composition of two functors.
data (g :.: h) = g :.: h
type instance F (g :.: h) a = F g (F h a)
type instance Dom (g :.: h) = Dom h
type instance Cod (g :.: h) = Cod g
instance (FunctorA g (F h a) (F h b), FunctorA h a b, Cod h ~ Dom g) => FunctorA (g :.: h) a b where
   (g :.: h) % f = g % (h % f)

-- |The constant functor.
data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x = Const
type instance F (Const c1 c2 x) a = x
type instance Dom (Const c1 c2 x) = c1
type instance Cod (Const c1 c2 x) = c2
instance (CategoryO c1 a, CategoryO c1 b, CategoryO c2 x) => FunctorA (Const c1 c2 x) a b where
  Const % f = id
  
-- |The covariant functor Hom(X,--)
data (x :*-: ((~>) :: * -> * -> *)) = HomX_
type instance F (x :*-: (~>)) a = x ~> a
type instance Dom (x :*-: (~>)) = (~>)
type instance Cod (x :*-: (~>)) = (->)
instance (CategoryO (~>) a, CategoryO (~>) b, CategoryA (~>) x a b) => FunctorA (x :*-: (~>)) a b where
  HomX_ % f = (f .)

-- |The contravariant functor Hom(--,X)
data (((~>) :: * -> * -> *) :-*: x) = Hom_X
type instance F ((~>) :-*: x) a = a ~> x
type instance Dom ((~>) :-*: x) = (~>)
type instance Cod ((~>) :-*: x) = (->)
instance (CategoryO (~>) a, CategoryO (~>) b, CategoryA (~>) a b x) => ContraFunctorA ((~>) :-*: x) a b where
  Hom_X -% f = (. f)