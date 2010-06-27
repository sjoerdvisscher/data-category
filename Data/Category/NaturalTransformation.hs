{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, ScopedTypeVariables, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.NaturalTransformation
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.NaturalTransformation where
  
import Prelude hiding ((.), id, Functor)

import Data.Category
import Data.Category.Functor


-- | @f :~> g@ is a natural transformation from functor f to functor g.
type f :~> g = (c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) => Nat c d f g

data Nat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  Nat :: (Functor f, Functor g, c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) 
    => f -> g -> (forall a. Obj c a -> Component f g a) -> Nat c d f g

-- | Natural transformations are built up of components, 
-- one for each object @z@ in the domain category of @f@ and @g@.
type Component f g z = Cod f (F f z) (F g z)


-- | Functor category D^C.
-- Objects of D^C are functors from C to D.
-- Arrows of D^C are natural transformations.
instance (Category c, Category d) => Category (Nat c d) where
  
  data Obj (Nat c d) a where
    NatO :: (Functor f, Dom f ~ c, Cod f ~ d) => f -> Obj (Nat c d) f
    
  src (Nat f _ _) = NatO f
  tgt (Nat _ g _) = NatO g
  
  id (NatO f)               = Nat f f $ \i -> id $ f %% i
  Nat _ h ngh . Nat f _ nfg = Nat f h $ \i -> ngh i . nfg i


-- | Horizontal composition of natural transformations.
o :: Category e => Nat d e j k -> Nat c d f g -> Nat c e (j :.: f) (k :.: g)
Nat j k njk `o` Nat f g nfg = Nat (j :.: f) (k :.: g) $ \x -> k % nfg x . njk (f %% x)


-- This data type can be used when creating data instances of @Nat@.
data Comp :: * -> * -> * -> * where
  Com :: Cod f (F f z) (F g z) -> Comp f g z

unCom :: Comp f g z -> Cod f (F f z) (F g z)
unCom (Com c) = c



-- | 'n ! a' returns the component for the object @a@ of a natural transformation @n@.
(!) :: (Cod f ~ d, Cod g ~ d) => Nat (~>) d f g -> Obj (~>) a -> d (F f a) (F g a)
Nat _ _ n ! x = n x


data Precompose :: * -> (* -> * -> *) -> * where
  Precompose :: (Functor f, Category d) => f -> Precompose f d

type instance Dom (Precompose f d) = Nat (Op (Cod f)) d
type instance Cod (Precompose f d) = Nat (Op (Dom f)) d
type instance F (Precompose f d) g = g :.: DualFunctor f

instance Functor (Precompose f d) where
  Precompose f %% NatO g = NatO $ g :.: DualFunctor f
  Precompose f % (Nat g h n) = Nat (g :.: DualFunctor f) (h :.: DualFunctor f) $ n . (DualFunctor f %%)


data Postcompose :: * -> (* -> * -> *) -> * where
  Postcompose :: (Functor f, Category c) => f -> Postcompose f c

type instance Dom (Postcompose f c) = Nat c (Dom f)
type instance Cod (Postcompose f c) = Nat c (Cod f)
type instance F (Postcompose f c) g = f :.: g

instance Functor (Postcompose f c) where
  Postcompose f %% NatO g = NatO $ f :.: g
  Postcompose f % (Nat g h n) = Nat (f :.: g) (f :.: h) $ (f %) . n


-- | A functor F: Op(C) -> Set is representable if it is naturally isomorphic to the contravariant hom-functor.
class Functor f => Representable f where
  type RepresentingObject f :: *
  represent   :: (Dom f ~ Op c) => f -> (c :-*: RepresentingObject f) :~> f
  unrepresent :: (Dom f ~ Op c) => f -> f :~> (c :-*: RepresentingObject f)

instance Category (~>) => Representable ((~>) :-*: x) where
  type RepresentingObject ((~>) :-*: x) = x
  represent   f = id $ NatO f
  unrepresent f = id $ NatO f


-- | The Yoneda embedding functor.
data Yoneda :: (* -> * -> *) -> * where
  Yoneda :: Category (~>) => Yoneda (~>)
  
type instance Dom (Yoneda (~>)) = (~>)
type instance Cod (Yoneda (~>)) = Nat (Op (~>)) (->)
type instance F (Yoneda (~>)) a = (~>) :-*: a

instance Functor (Yoneda (~>)) where
  Yoneda %% x = NatO $ Hom_X x
  Yoneda % f = Nat (Hom_X $ src f) (Hom_X $ tgt f) $ \_ -> (f .)

