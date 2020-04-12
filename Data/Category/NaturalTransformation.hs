{-# LANGUAGE TypeOperators, TypeFamilies, PatternSynonyms, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs, LiberalTypeSynonyms, NoImplicitPrelude #-}
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
  , (!)
  , o
  , natId
  , srcF
  , tgtF

  -- * Functor category
  , Nat(..)
  , Endo
  , Presheaves
  , Profunctors

  -- * Functor isomorphisms
  , compAssoc
  , compAssocInv
  , idPrecomp
  , idPrecompInv
  , idPostcomp
  , idPostcompInv
  , constPrecompIn
  , constPrecompOut
  , constPostcompIn
  , constPostcompOut

  -- * Related functors
  , FunctorCompose(..)
  , EndoFunctorCompose
  , Precompose, pattern Precompose
  , Postcompose, pattern Postcompose
  , Wrap(..)
  , Apply(..)
  , Tuple(..)

) where

import Data.Category
import Data.Category.Functor
import Data.Category.Product

infixl 9 !

-- | @f :~> g@ is a natural transformation from functor f to functor g.
type f :~> g = forall c d. (c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) => Nat c d f g

-- | Natural transformations are built up of components,
-- one for each object @z@ in the domain category of @f@ and @g@.
data Nat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  Nat :: (Functor f, Functor g, c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g)
    => f -> g -> (forall z. Obj c z -> Component f g z) -> Nat c d f g


-- | A component for an object @z@ is an arrow from @F z@ to @G z@.
type Component f g z = Cod f (f :% z) (g :% z)

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

pattern NatId :: Functor f => f -> Nat (Dom f) (Cod f) f f
pattern NatId f <- Nat f _ _ where 
  NatId f = Nat f f (\i -> f % i)

srcF :: Nat c d f g -> f
srcF (Nat f _ _) = f

tgtF :: Nat c d f g -> g
tgtF (Nat _ g _) = g

-- | Functor category D^C.
-- Objects of D^C are functors from C to D.
-- Arrows of D^C are natural transformations.
instance Category d => Category (Nat c d) where

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


constPrecompIn :: Nat j d (f :.: Const j c x) g -> Nat j d (Const j d (f :% x)) g
constPrecompIn (Nat (f :.: Const x) g n) = Nat (Const (f % x)) g n

constPrecompOut :: Nat j d f (g :.: Const j c x) -> Nat j d f (Const j d (g :% x))
constPrecompOut (Nat f (g :.: Const x) n) = Nat f (Const (g % x)) n

constPostcompIn :: Nat j d (Const k d x :.: f) g -> Nat j d (Const j d x) g
constPostcompIn (Nat (Const x :.: _) g n) = Nat (Const x) g n

constPostcompOut :: Nat j d f (Const k d x :.: g) -> Nat j d f (Const j d x)
constPostcompOut (Nat f (Const x :.: _) n) = Nat f (Const x) n


data FunctorCompose (c :: * -> * -> *) (d :: * -> * -> *) (e :: * -> * -> *) = FunctorCompose

-- | Composition of functors is a functor.
instance (Category c, Category d, Category e) => Functor (FunctorCompose c d e) where
  type Dom (FunctorCompose c d e) = Nat d e :**: Nat c d
  type Cod (FunctorCompose c d e) = Nat c e
  type FunctorCompose c d e :% (f, g) = f :.: g

  FunctorCompose % (n1 :**: n2) = n1 `o` n2


-- | The category of endofunctors.
type Endo k = Nat k k
-- | Composition of endofunctors is a functor.
type EndoFunctorCompose k = FunctorCompose k k k

type Presheaves k = Nat (Op k) (->)

type Profunctors c d = Nat (Op d :**: c) (->)

-- | @Precompose f e@ is the functor such that @Precompose f e :% g = g :.: f@,
--   for functors @g@ that compose with @f@ and with codomain @e@.
type Precompose f e = FunctorCompose (Dom f) (Cod f) e :.: Tuple2 (Nat (Cod f) e) (Nat (Dom f) (Cod f)) f
pattern Precompose :: (Category e, Functor f) => f -> Precompose f e
pattern Precompose f = FunctorCompose :.: Tuple2 (NatId f)

-- | @Postcompose f c@ is the functor such that @Postcompose f c :% g = f :.: g@,
--   for functors @g@ that compose with @f@ and with domain @c@.
type Postcompose f c = FunctorCompose c (Dom f) (Cod f) :.: Tuple1 (Nat (Dom f) (Cod f)) (Nat c (Dom f)) f
pattern Postcompose :: (Category e, Functor f) => f -> Postcompose f e
pattern Postcompose f = FunctorCompose :.: Tuple1 (NatId f)


data Wrap f h = Wrap f h

-- | @Wrap f h@ is the functor such that @Wrap f h :% g = f :.: g :.: h@,
--   for functors @g@ that compose with @f@ and @h@.
instance (Functor f, Functor h) => Functor (Wrap f h) where
  type Dom (Wrap f h) = Nat (Cod h) (Dom f)
  type Cod (Wrap f h) = Nat (Dom h) (Cod f)
  type Wrap f h :% g = f :.: g :.: h

  Wrap f h % n = natId f `o` n `o` natId h


data Apply (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Apply
-- | 'Apply' is a bifunctor, @Apply :% (f, a)@ applies @f@ to @a@, i.e. @f :% a@.
instance (Category c1, Category c2) => Functor (Apply c1 c2) where
  type Dom (Apply c1 c2) = Nat c2 c1 :**: c2
  type Cod (Apply c1 c2) = c1
  type Apply c1 c2 :% (f, a) = f :% a
  Apply % (l :**: r) = l ! r

data Tuple (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Tuple
-- | 'Tuple' converts an object @a@ to the functor 'Tuple1' @a@.
instance (Category c1, Category c2) => Functor (Tuple c1 c2) where
  type Dom (Tuple c1 c2) = c1
  type Cod (Tuple c1 c2) = Nat c2 (c1 :**: c2)
  type Tuple c1 c2 :% a = Tuple1 c1 c2 a
  Tuple % f = Nat (Tuple1 (src f)) (Tuple1 (tgt f)) (\z -> f :**: z)
