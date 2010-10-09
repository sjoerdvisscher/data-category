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
module Data.Category.NaturalTransformation (

  -- * Natural transformations
    (:~>)
  , Component
  , Com(..)
  , (!)
  , o
  , natId

  -- * Functor category
  , Nat(..)
  , Endo
    
  -- * Related functors
  , FunctorCompose(..)
  , Precompose(..)
  , Postcompose(..)
  , Wrap(..)
  
  -- ** Yoneda
  , YonedaEmbedding(..)
  , Yoneda
  , fromYoneda
  , toYoneda
  
) where
  
import Prelude hiding ((.), id, Functor)

import Data.Category
import Data.Category.Functor
import Data.Category.Product

infixl 9 !

-- | @f :~> g@ is a natural transformation from functor f to functor g.
type f :~> g = (c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) => Nat c d f g

-- | Natural transformations are built up of components, 
-- one for each object @z@ in the domain category of @f@ and @g@.
data Nat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  Nat :: (Functor f, Functor g, c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) 
    => f -> g -> (forall z. Obj c z -> Component f g z) -> Nat c d f g


-- | A component for an object @z@ is an arrow from @F z@ to @G z@.
type Component f g z = Cod f (f :% z) (g :% z)

-- | A newtype wrapper for components,
--   which can be useful for helper functions dealing with components.
newtype Com f g z = Com { unCom :: Component f g z }

-- | 'n ! a' returns the component for the object @a@ of a natural transformation @n@.
--   This can be generalized to any arrow (instead of just identity arrows).
(!) :: (Category c, Category d) => Nat c d f g -> c a b -> d (f :% a) (g :% b)
Nat f _ n ! h = n (tgt h) . f % h -- or g % h . n (src h), or n h when h is an identity arrow


-- | Horizontal composition of natural transformations.
o :: (Category c, Category d, Category e) => Nat d e j k -> Nat c d f g -> Nat c e (j :.: f) (k :.: g)
njk@(Nat j k _) `o` nfg@(Nat f g _) = Nat (j :.: f) (k :.: g) $ (njk !) . (nfg !)
-- Nat j k njk `o` Nat f g nfg = Nat (j :.: f) (k :.: g) $ \x -> njk (g % x) . j % nfg x -- or k % nfg x . njk (f % x)

-- | The identity natural transformation of a functor.
natId :: Functor f => f -> Nat (Dom f) (Cod f) f f
natId f = Nat f f $ \i -> f % i


-- | Functor category D^C.
-- Objects of D^C are functors from C to D.
-- Arrows of D^C are natural transformations.
instance (Category c, Category d) => Category (Nat c d) where
  
  src (Nat f _ _)           = natId f
  tgt (Nat _ g _)           = natId g
  
  Nat _ h ngh . Nat f _ nfg = Nat f h $ \i -> ngh i . nfg i


-- | The category of endofunctors.
type Endo (~>) = Nat (~>) (~>)


-- | Composition of endofunctors is a functor.
data FunctorCompose ((~>) :: * -> * -> *) = FunctorCompose

type instance Dom (FunctorCompose (~>)) = Endo (~>) :**: Endo (~>)
type instance Cod (FunctorCompose (~>)) = Endo (~>)
type instance FunctorCompose (~>) :% (f, g) = f :.: g

instance Category (~>) => Functor (FunctorCompose (~>)) where
  FunctorCompose % (n1 :**: n2) = n1 `o` n2


-- | @Precompose f d@ is the functor such that @Precompose f d :% g = g :.: f@, 
--   for functors @g@ that compose with @f@ and with codomain @d@.
data Precompose :: * -> (* -> * -> *) -> * where
  Precompose :: f -> Precompose f d

type instance Dom (Precompose f d) = Nat (Cod f) d
type instance Cod (Precompose f d) = Nat (Dom f) d
type instance Precompose f d :% g = g :.: f

instance (Functor f, Category d) => Functor (Precompose f d) where
  Precompose f % (Nat g h n) = Nat (g :.: f) (h :.: f) $ n . (f %)


-- | @Postcompose f c@ is the functor such that @Postcompose f c :% g = f :.: g@, 
--   for functors @g@ that compose with @f@ and with domain @c@.
data Postcompose :: * -> (* -> * -> *) -> * where
  Postcompose :: f -> Postcompose f c

type instance Dom (Postcompose f c) = Nat c (Dom f)
type instance Cod (Postcompose f c) = Nat c (Cod f)
type instance Postcompose f c :% g = f :.: g

instance (Functor f, Category c) => Functor (Postcompose f c) where
  Postcompose f % (Nat g h n) = Nat (f :.: g) (f :.: h) $ (f %) . n


-- | @Wrap f h@ is the functor such that @Wrap f h :% g = f :.: g :.: h@, 
--   for functors @g@ that compose with @f@ and @h@.
data Wrap f h = Wrap f h

type instance Dom (Wrap f h) = Nat (Cod h) (Dom f)
type instance Cod (Wrap f h) = Nat (Dom h) (Cod f)
type instance Wrap f h :% g = f :.: g :.: h

instance (Functor f, Functor h) => Functor (Wrap f h) where
  Wrap f h % (Nat g1 g2 n) = Nat (f :.: g1 :.: h) (f :.: g2 :.: h) $ (f %) . n . (h %)


-- | A functor F: Op(C) -> Set is representable if it is naturally isomorphic to the contravariant hom-functor.
class Functor f => Representable f where
  type RepresentingObject f :: *
  represent   :: (Dom f ~ Op c) => f -> (c :-*: RepresentingObject f) :~> f
  unrepresent :: (Dom f ~ Op c) => f -> f :~> (c :-*: RepresentingObject f)

instance Category (~>) => Representable ((~>) :-*: x) where
  type RepresentingObject ((~>) :-*: x) = x
  represent   f = natId f
  unrepresent f = natId f


-- | The Yoneda embedding functor.
data YonedaEmbedding :: (* -> * -> *) -> * where
  YonedaEmbedding :: Category (~>) => YonedaEmbedding (~>)
  
type instance Dom (YonedaEmbedding (~>)) = Op (~>)
type instance Cod (YonedaEmbedding (~>)) = Nat (~>) (->)
type instance YonedaEmbedding (~>) :% a = a :*-: (~>)

instance Category (~>) => Functor (YonedaEmbedding (~>)) where
  YonedaEmbedding % (Op f) = Nat (HomX_ $ tgt f) (HomX_ $ src f) $ \_ -> (. f)


type Yoneda f a = Nat (Dom f) (->) (a :*-: Dom f) f
  
fromYoneda :: Yoneda f a -> f :% a
fromYoneda (Nat (HomX_ a) _ n) = n a a

toYoneda :: (Functor f, Cod f ~ (->)) => f -> Obj (Dom f) a -> f :% a -> Yoneda f a
toYoneda f a fa = Nat (HomX_ a) f $ \_ -> \h -> (f % h) fa

-- type Yoneda (~>) f a = Nat (Op (~>)) (->) ((~>) :-*: a) f
--   
-- fromYoneda :: (Dom f ~ Op (~>)) => Yoneda (~>) f a -> f :% a
-- fromYoneda (Nat (Hom_X a) _ n) = n (Op a) a
-- 
-- toYoneda :: (Category (~>), Functor f, Dom f ~ Op (~>), Cod f ~ (->)) => f -> Obj (Op (~>)) a -> f :% a -> Yoneda (~>) f a
-- toYoneda f (Op a) fa = Nat (Hom_X a) f $ \_ -> \h -> (f % Op h) fa