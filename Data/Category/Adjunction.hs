{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleContexts, ScopedTypeVariables, RankNTypes, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Adjunction
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Adjunction (

  -- * Adjunctions
    Adjunction(..)
  , mkAdjunction
  , mkAdjunctionUnits
  , mkAdjunctionInit
  , mkAdjunctionTerm

  , leftAdjunct
  , rightAdjunct
  , adjunctionUnit
  , adjunctionCounit

  -- * Adjunctions as a category
  , idAdj
  , composeAdj
  , AdjArrow(..)

  -- * Examples
  , precomposeAdj
  , postcomposeAdj
  , contAdj

) where

import Data.Category
import Data.Category.Functor
import Data.Category.Product
import Data.Category.NaturalTransformation

data Adjunction c d f g = (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => Adjunction
  { leftAdjoint  :: f
  , rightAdjoint :: g
  , leftAdjunctN  :: Profunctors c d (Costar f) (Star g)
  , rightAdjunctN :: Profunctors c d (Star g) (Costar f)
  }

-- | Make an adjunction from the hom-set isomorphism.
mkAdjunction :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a b. Obj d a -> c (f :% a) b -> d a (g :% b))
  -> (forall a b. Obj c b -> d a (g :% b) -> c (f :% a) b)
  -> Adjunction c d f g
mkAdjunction f g l r = Adjunction f g (Nat (Costar f) (Star g) (\(Op a :**: _) -> l a)) (Nat (Star g) (Costar f) (\(_ :**: b) -> r b))

-- | Make an adjunction from the unit and counit.
mkAdjunctionUnits :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a. Obj d a -> Component (Id d) (g :.: f) a)
  -> (forall a. Obj c a -> Component (f :.: g) (Id c) a)
  -> Adjunction c d f g
mkAdjunctionUnits f g un coun = mkAdjunction f g (\a h -> (g % h) . un a) (\b h -> coun b . (f % h))

-- | Make an adjunction from an initial universal property.
mkAdjunctionInit :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a. Obj d a -> d a (g :% (f :% a)))
  -> (forall a b. Obj c b -> d a (g :% b) -> c (f :% a) b)
  -> Adjunction c d f g
mkAdjunctionInit f g un adj = mkAdjunction f g (\a h -> (g % h) . un a) adj

-- | Make an adjunction from a terminal universal property.
mkAdjunctionTerm :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a b. Obj d a -> c (f :% a) b -> d a (g :% b))
  -> (forall b. Obj c b -> c (f :% (g :% b)) b)
  -> Adjunction c d f g
mkAdjunctionTerm f g adj coun = mkAdjunction f g adj (\b h -> coun b . (f % h))

leftAdjunct :: Adjunction c d f g -> Obj d a -> c (f :% a) b -> d a (g :% b)
leftAdjunct (Adjunction _ _ l _) a h = (l ! (Op a :**: tgt h)) h
rightAdjunct :: Adjunction c d f g -> Obj c b -> d a (g :% b) -> c (f :% a) b
rightAdjunct (Adjunction _ _ _ r) b h = (r ! (Op (src h) :**: b)) h

adjunctionUnit :: Adjunction c d f g -> Nat d d (Id d) (g :.: f)
adjunctionUnit adj@(Adjunction f g _ _) = Nat Id (g :.: f) (\a -> leftAdjunct adj a (f % a))
adjunctionCounit :: Adjunction c d f g -> Nat c c (f :.: g) (Id c)
adjunctionCounit adj@(Adjunction f g _ _) = Nat (f :.: g) Id (\b -> rightAdjunct adj b (g % b))


idAdj :: Category k => Adjunction k k (Id k) (Id k)
idAdj = mkAdjunction Id Id (\_ f -> f) (\_ f -> f)

composeAdj :: Adjunction d e f g -> Adjunction c d f' g' -> Adjunction c e (f' :.: f) (g :.: g')
composeAdj l@(Adjunction f g _ _) r@(Adjunction f' g' _ _) = mkAdjunction (f' :.: f) (g :.: g')
  (\a -> leftAdjunct l a . leftAdjunct r (f % a)) (\b -> rightAdjunct r b . rightAdjunct l (g' % b))


data AdjArrow c d where
  AdjArrow :: (Category c, Category d) => Adjunction c d f g -> AdjArrow c d

-- | The category with categories as objects and adjunctions as arrows.
instance Category AdjArrow where

  src (AdjArrow (Adjunction _ _ _ _)) = AdjArrow idAdj
  tgt (AdjArrow (Adjunction _ _ _ _)) = AdjArrow idAdj

  AdjArrow x . AdjArrow y = AdjArrow (composeAdj x y)



precomposeAdj :: Category e => Adjunction c d f g -> Adjunction (Nat c e) (Nat d e) (Precompose g e) (Precompose f e)
precomposeAdj adj@(Adjunction f g _ _) = mkAdjunctionUnits
  (Precompose g)
  (Precompose f)
  (\nh@(Nat h _ _) -> compAssocInv h g f . (nh `o` adjunctionUnit adj) . idPrecompInv h)
  (\nh@(Nat h _ _) -> idPrecomp h . (nh `o` adjunctionCounit adj) . compAssoc h f g)

postcomposeAdj :: Category e => Adjunction c d f g -> Adjunction (Nat e c) (Nat e d) (Postcompose f e) (Postcompose g e)
postcomposeAdj adj@(Adjunction f g _ _) = mkAdjunctionUnits
  (Postcompose f)
  (Postcompose g)
  (\nh@(Nat h _ _) -> compAssoc g f h . (adjunctionUnit adj `o` nh) . idPostcompInv h)
  (\nh@(Nat h _ _) -> idPostcomp h . (adjunctionCounit adj `o` nh) . compAssocInv f g h)

contAdj :: Adjunction (Op (->)) (->) (Opposite ((->) :-*: r) :.: OpOpInv (->)) ((->) :-*: r)
contAdj = mkAdjunction
  (Opposite (Hom_X (\x -> x)) :.: OpOpInv)
  (Hom_X (\x -> x))
  (\_ -> \(Op f) -> \b a -> f a b)
  (\_ -> \f -> Op (\b a -> f a b))
