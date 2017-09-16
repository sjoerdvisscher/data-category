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

  , leftAdjunct
  , rightAdjunct
  , adjunctionUnit
  , adjunctionCounit

  -- * Adjunctions as a category
  , idAdj
  , composeAdj
  , AdjArrow(..)

  -- * Adjunctions from universal morphisms
  , initialPropAdjunction
  , terminalPropAdjunction

  -- * Universal morphisms from adjunctions
  , adjunctionInitialProp
  , adjunctionTerminalProp

  -- * Examples
  , precomposeAdj
  , postcomposeAdj
  , contAdj

) where

import Data.Category
import Data.Category.Functor
import Data.Category.Product
import Data.Category.NaturalTransformation
import Data.Category.RepresentableFunctor

data Adjunction c d f g = (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => Adjunction
  { leftAdjoint  :: f
  , rightAdjoint :: g
  , leftAdjunctN  :: Profunctors c d (Costar f) (Star g)
  , rightAdjunctN :: Profunctors c d (Star g) (Costar f)
  }

mkAdjunction :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a b. Obj d a -> c (f :% a) b -> d a (g :% b))
  -> (forall a b. Obj c b -> d a (g :% b) -> c (f :% a) b)
  -> Adjunction c d f g
mkAdjunction f g l r = Adjunction f g (Nat (costar f) (star g) (\(Op a :**: _) -> l a)) (Nat (star g) (costar f) (\(_ :**: b) -> r b))

mkAdjunctionUnits :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a. Obj d a -> Component (Id d) (g :.: f) a)
  -> (forall a. Obj c a -> Component (f :.: g) (Id c) a)
  -> Adjunction c d f g
mkAdjunctionUnits f g un coun = mkAdjunction f g (\a h -> (g % h) . un a) (\b h -> coun b . (f % h))

leftAdjunct :: Adjunction c d f g -> Obj d a -> c (f :% a) b -> d a (g :% b)
leftAdjunct (Adjunction _ _ l _) a h = (l ! (Op a :**: tgt h)) h
rightAdjunct :: Adjunction c d f g -> Obj c b -> d a (g :% b) -> c (f :% a) b
rightAdjunct (Adjunction _ _ _ r) b h = (r ! (Op (src h) :**: b)) h

adjunctionUnit :: Adjunction c d f g -> Nat d d (Id d) (g :.: f)
adjunctionUnit adj@(Adjunction f g _ _) = Nat Id (g :.: f) (\a -> leftAdjunct adj a (f % a))
adjunctionCounit :: Adjunction c d f g -> Nat c c (f :.: g) (Id c)
adjunctionCounit adj@(Adjunction f g _ _) = Nat (f :.: g) Id (\b -> rightAdjunct adj b (g % b))

-- Each pair (FY, unit_Y) is an initial morphism from Y to G.
adjunctionInitialProp :: Adjunction c d f g -> Obj d y -> InitialUniversal y g (f :% y)
adjunctionInitialProp adj@(Adjunction f g _ _) y = initialUniversal g (f % y) (adjunctionUnit adj ! y) (rightAdjunct adj)

-- Each pair (GX, counit_X) is a terminal morphism from F to X.
adjunctionTerminalProp :: Adjunction c d f g -> Obj c x -> TerminalUniversal x f (g :% x)
adjunctionTerminalProp adj@(Adjunction f g _ _) x = terminalUniversal f (g % x) (adjunctionCounit adj ! x) (leftAdjunct adj)



initialPropAdjunction :: forall f g c d. (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall y. Obj d y -> InitialUniversal y g (f :% y)) -> Adjunction c d f g
initialPropAdjunction f g univ = mkAdjunctionUnits f g
  (universalElement . univ)
  (\a -> represent (univ (g % a)) a (g % a))

terminalPropAdjunction :: forall f g c d. (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall x. Obj c x -> TerminalUniversal x f (g :% x)) -> Adjunction c d f g
terminalPropAdjunction f g univ = mkAdjunctionUnits f g
  (\a -> unOp (represent (univ (f % a)) (Op a) (f % a)))
  (universalElement . univ)


idAdj :: Category k => Adjunction k k (Id k) (Id k)
idAdj = mkAdjunction Id Id (\_ f -> f) (\_ f -> f)

composeAdj :: Adjunction d e f g -> Adjunction c d f' g' -> Adjunction c e (f' :.: f) (g :.: g')
composeAdj l@(Adjunction f g _ _) r@(Adjunction f' g' _ _) = mkAdjunction (f' :.: f) (g :.: g')
  (\a -> leftAdjunct l a . leftAdjunct r (f % a)) (\b -> rightAdjunct r b . rightAdjunct l (g' % b))


data AdjArrow c d where
  AdjArrow :: (Category c, Category d) => Adjunction c d f g -> AdjArrow (CatW c) (CatW d)

-- | The category with categories as objects and adjunctions as arrows.
instance Category AdjArrow where

  src (AdjArrow (Adjunction _ _ _ _)) = AdjArrow idAdj
  tgt (AdjArrow (Adjunction _ _ _ _)) = AdjArrow idAdj

  AdjArrow x . AdjArrow y = AdjArrow (composeAdj x y)



precomposeAdj :: Category e => Adjunction c d f g -> Adjunction (Nat c e) (Nat d e) (Precompose g e) (Precompose f e)
precomposeAdj adj@(Adjunction f g _ _) = mkAdjunctionUnits
  (precompose g)
  (precompose f)
  (\nh@(Nat h _ _) -> compAssocInv h g f . (nh `o` adjunctionUnit adj) . idPrecompInv h)
  (\nh@(Nat h _ _) -> idPrecomp h . (nh `o` adjunctionCounit adj) . compAssoc h f g)

postcomposeAdj :: Category e => Adjunction c d f g -> Adjunction (Nat e c) (Nat e d) (Postcompose f e) (Postcompose g e)
postcomposeAdj adj@(Adjunction f g _ _) = mkAdjunctionUnits
  (postcompose f)
  (postcompose g)
  (\nh@(Nat h _ _) -> compAssoc g f h . (adjunctionUnit adj `o` nh) . idPostcompInv h)
  (\nh@(Nat h _ _) -> idPostcomp h . (adjunctionCounit adj `o` nh) . compAssocInv f g h)

contAdj :: Adjunction (Op (->)) (->) (Opposite ((->) :-*: r) :.: OpOpInv (->)) ((->) :-*: r)
contAdj = mkAdjunction
  (Opposite (hom_X (\x -> x)) :.: OpOpInv)
  (hom_X (\x -> x))
  (\_ -> \(Op f) -> \b a -> f a b)
  (\_ -> \f -> Op (\b a -> f a b))