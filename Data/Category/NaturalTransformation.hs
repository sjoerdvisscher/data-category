{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.NaturalTransformation
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
  , srcF
  , tgtF

  -- * Functor category
  , Nat(..)
  , Endo
  
  -- * Functor isomorphisms
  , compAssoc
  , compAssocInv
  , idPrecomp
  , idPrecompInv
  , idPostcomp
  , idPostcompInv
  , constPrecomp
  , constPrecompInv
  , constPostcomp
  , constPostcompInv
    
  -- * Related functors
  , FunctorCompose(..)
  , Precompose(..)
  , Postcompose(..)
  , Wrap(..)
  
) where
  
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
njk@(Nat j k _) `o` nfg@(Nat f g _) = Nat (j :.: f) (k :.: g) ((njk !) . (nfg !))
-- Nat j k njk `o` Nat f g nfg = Nat (j :.: f) (k :.: g) (\x -> njk (g % x) . j % nfg x) -- or k % nfg x . njk (f % x)

-- | The identity natural transformation of a functor.
natId :: Functor f => f -> Nat (Dom f) (Cod f) f f
natId f = Nat f f (\i -> f % i)

srcF :: Nat c d f g -> f
srcF (Nat f _ _) = f

tgtF :: Nat c d f g -> g
tgtF (Nat _ g _) = g

-- | Functor category D^C.
-- Objects of D^C are functors from C to D.
-- Arrows of D^C are natural transformations.
instance (Category c, Category d) => Category (Nat c d) where
  
  src (Nat f _ _)           = natId f
  tgt (Nat _ g _)           = natId g
  
  Nat _ h ngh . Nat f _ nfg = Nat f h (\i -> ngh i . nfg i)


compAssoc :: (Functor f, Functor g, Functor h, Dom f ~ Cod g, Dom g ~ Cod h)
          => f -> g -> h -> Nat (Dom h) (Cod f) ((f :.: g) :.: h) (f :.: (g :.: h))
compAssoc f g h = Nat ((f :.: g) :.: h) (f :.: (g :.: h)) (\i -> f % g % h % i)

compAssocInv :: (Functor f, Functor g, Functor h, Dom f ~ Cod g, Dom g ~ Cod h)
             => f -> g -> h -> Nat (Dom h) (Cod f) (f :.: (g :.: h)) ((f :.: g) :.: h)
compAssocInv f g h = Nat (f :.: (g :.: h)) ((f :.: g) :.: h) (\i -> f % g % h % i)

idPrecomp :: Functor f => f -> Nat (Dom f) (Cod f) (f :.: Id (Dom f)) f
idPrecomp f = Nat (f :.: Id) f (f %)

idPrecompInv :: Functor f => f -> Nat (Dom f) (Cod f) f (f :.: Id (Dom f))
idPrecompInv f = Nat f (f :.: Id) (f %)

idPostcomp :: Functor f => f -> Nat (Dom f) (Cod f) (Id (Cod f) :.: f) f
idPostcomp f = Nat (Id :.: f) f (f %)

idPostcompInv :: Functor f => f -> Nat (Dom f) (Cod f) f (Id (Cod f) :.: f)
idPostcompInv f = Nat f (Id :.: f) (f %)


constPrecomp :: (Category c1, Functor f) => Const c1 (Dom f) x -> f -> Nat c1 (Cod f) (f :.: Const c1 (Dom f) x) (Const c1 (Cod f) (f :% x))
constPrecomp (Const x) f = let fx = f % x in Nat (f :.: Const x) (Const fx) (\_ -> fx)

constPrecompInv :: (Category c1, Functor f) => Const c1 (Dom f) x -> f -> Nat c1 (Cod f) (Const c1 (Cod f) (f :% x)) (f :.: Const c1 (Dom f) x)
constPrecompInv (Const x) f = let fx = f % x in Nat (Const fx) (f :.: Const x) (\_ -> fx)

constPostcomp :: Functor f => Const (Cod f) c2 x -> f -> Nat (Dom f) c2 (Const (Cod f) c2 x :.: f) (Const (Dom f) c2 x)
constPostcomp (Const x) f = Nat (Const x :.: f) (Const x) (\_ -> x)

constPostcompInv :: Functor f => Const (Cod f) c2 x -> f -> Nat (Dom f) c2 (Const (Dom f) c2 x) (Const (Cod f) c2 x :.: f)
constPostcompInv (Const x) f = Nat (Const x) (Const x :.: f) (\_ -> x)



-- | The category of endofunctors.
type Endo k = Nat k k


data FunctorCompose (k :: * -> * -> *) = FunctorCompose

-- | Composition of endofunctors is a functor.
instance Category k => Functor (FunctorCompose k) where
  type Dom (FunctorCompose k) = Endo k :**: Endo k
  type Cod (FunctorCompose k) = Endo k
  type FunctorCompose k :% (f, g) = f :.: g
  
  FunctorCompose % (n1 :**: n2) = n1 `o` n2


data Precompose :: * -> (* -> * -> *) -> * where
  Precompose :: f -> Precompose f d

-- | @Precompose f d@ is the functor such that @Precompose f d :% g = g :.: f@,
--   for functors @g@ that compose with @f@ and with codomain @d@.
instance (Functor f, Category d) => Functor (Precompose f d) where
  type Dom (Precompose f d) = Nat (Cod f) d
  type Cod (Precompose f d) = Nat (Dom f) d
  type Precompose f d :% g = g :.: f
  
  Precompose f % n = n `o` natId f


data Postcompose :: * -> (* -> * -> *) -> * where
  Postcompose :: f -> Postcompose f c

-- | @Postcompose f c@ is the functor such that @Postcompose f c :% g = f :.: g@,
--   for functors @g@ that compose with @f@ and with domain @c@.
instance (Functor f, Category c) => Functor (Postcompose f c) where
  type Dom (Postcompose f c) = Nat c (Dom f)
  type Cod (Postcompose f c) = Nat c (Cod f)
  type Postcompose f c :% g = f :.: g
  
  Postcompose f % n = natId f `o` n


data Wrap f h = Wrap f h

-- | @Wrap f h@ is the functor such that @Wrap f h :% g = f :.: g :.: h@,
--   for functors @g@ that compose with @f@ and @h@.
instance (Functor f, Functor h) => Functor (Wrap f h) where
  type Dom (Wrap f h) = Nat (Cod h) (Dom f)
  type Cod (Wrap f h) = Nat (Dom h) (Cod f)
  type Wrap f h :% g = f :.: g :.: h
  
  Wrap f h % n = natId f `o` n `o` natId h
