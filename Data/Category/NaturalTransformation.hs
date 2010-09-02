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

  -- * Functor category
  , Nat(..)
  , Obj(..)
  , Endo
    
  -- * Related functors
  , Precompose(..)
  , Postcompose(..)
  , YonedaEmbedding(..)
  
) where
  
import Prelude hiding ((.), id, Functor)

import Data.Category
import Data.Category.Functor

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
(!) :: (Cod f ~ d, Cod g ~ d) => Nat (~>) d f g -> Obj (~>) a -> d (f :% a) (g :% a)
Nat _ _ n ! x = n x


-- | Horizontal composition of natural transformations.
o :: Category e => Nat d e j k -> Nat c d f g -> Nat c e (j :.: f) (k :.: g)
Nat j k njk `o` Nat f g nfg = Nat (j :.: f) (k :.: g) $ \x -> k % nfg x . njk (f %% x)


-- | Functor category D^C.
-- Objects of D^C are functors from C to D.
-- Arrows of D^C are natural transformations.
instance (Category c, Category d) => Category (Nat c d) where
  
  data Obj (Nat c d) a where
    NatO :: (Functor f, Dom f ~ c, Cod f ~ d) => f -> Obj (Nat c d) f
    
  src (Nat f _ _) = NatO f
  tgt (Nat _ g _) = NatO g
  
  id (NatO f)               = Nat f f $ \i -> f % id i
  Nat _ h ngh . Nat f _ nfg = Nat f h $ \i -> ngh i . nfg i


-- | The category of endofunctors.
type Endo (~>) = Nat (~>) (~>)



-- | @Precompose f d@ is the functor such that @Precompose f d :% g = g :.: f@, 
--   for functors @g@ that compose with @f@ and with codomain @d@.
data Precompose :: * -> (* -> * -> *) -> * where
  Precompose :: f -> Precompose f d

type instance Dom (Precompose f d) = Nat (Cod f) d
type instance Cod (Precompose f d) = Nat (Dom f) d
type instance Precompose f d :% g = g :.: f

instance (Functor f, Category d) => Functor (Precompose f d) where
  Precompose f % (Nat g h n) = Nat (g :.: f) (h :.: f) $ n . (f %%)


-- | @Postcompose f c@ is the functor such that @Postcompose f c :% g = f :.: g@, 
--   for functors @g@ that compose with @f@ and with domain @c@.
data Postcompose :: * -> (* -> * -> *) -> * where
  Postcompose :: f -> Postcompose f c

type instance Dom (Postcompose f c) = Nat c (Dom f)
type instance Cod (Postcompose f c) = Nat c (Cod f)
type instance Postcompose f c :% g = f :.: g

instance (Functor f, Category c) => Functor (Postcompose f c) where
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
data YonedaEmbedding :: (* -> * -> *) -> * where
  YonedaEmbedding :: Category (~>) => YonedaEmbedding (~>)
  
type instance Dom (YonedaEmbedding (~>)) = (~>)
type instance Cod (YonedaEmbedding (~>)) = Nat (Op (~>)) (->)
type instance YonedaEmbedding (~>) :% a = (~>) :-*: a

instance Category (~>) => Functor (YonedaEmbedding (~>)) where
  YonedaEmbedding % f = Nat (Hom_X $ src f) (Hom_X $ tgt f) $ \_ -> (f .)
