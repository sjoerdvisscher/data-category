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

  , leftAdjunct
  , rightAdjunct

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
  , unit         :: Nat d d (Id d) (g :.: f)
  , counit       :: Nat c c (f :.: g) (Id c)
  }

mkAdjunction :: (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g
  -> (forall a. Obj d a -> Component (Id d) (g :.: f) a)
  -> (forall a. Obj c a -> Component (f :.: g) (Id c) a)
  -> Adjunction c d f g
mkAdjunction f g un coun = Adjunction f g (Nat Id (g :.: f) un) (Nat (f :.: g) Id coun)

leftAdjunct :: Adjunction c d f g -> Obj d a -> c (f :% a) b -> d a (g :% b)
leftAdjunct (Adjunction _ g un _) i h = (g % h) . (un ! i)
rightAdjunct :: Adjunction c d f g -> Obj c b -> d a (g :% b) -> c (f :% a) b
rightAdjunct (Adjunction f _ _ coun) i h = (coun ! i) . (f % h)

leftAdjunctN :: Adjunction c d f g -> Profunctors c d (Costar f) (Star g)
leftAdjunctN (Adjunction f g un _) = Nat (costar f) (star g) (\(Op a :**: _) h -> (g % h) . (un ! a))
rightAdjunctN :: Adjunction c d f g -> Profunctors c d (Star g) (Costar f)
rightAdjunctN (Adjunction f g _ coun) = Nat (star g) (costar f) (\(_ :**: b) h -> (coun ! b) . (f % h))


-- Each pair (FY, unit_Y) is an initial morphism from Y to G.
adjunctionInitialProp :: Adjunction c d f g -> Obj d y -> InitialUniversal y g (f :% y)
adjunctionInitialProp adj@(Adjunction f g un _) y = initialUniversal g (f % y) (un ! y) (rightAdjunct adj)

-- Each pair (GX, counit_X) is a terminal morphism from F to X.
adjunctionTerminalProp :: Adjunction c d f g -> Obj c x -> TerminalUniversal x f (g :% x)
adjunctionTerminalProp adj@(Adjunction f g _ coun) x = terminalUniversal f (g % x) (coun ! x) (leftAdjunct adj)



initialPropAdjunction :: forall f g c d. (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall y. Obj d y -> InitialUniversal y g (f :% y)) -> Adjunction c d f g
initialPropAdjunction f g univ = mkAdjunction f g
  (universalElement . univ)
  (\a -> represent (univ (g % a)) a (g % a))

terminalPropAdjunction :: forall f g c d. (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall x. Obj c x -> TerminalUniversal x f (g :% x)) -> Adjunction c d f g
terminalPropAdjunction f g univ = mkAdjunction f g
  (\a -> unOp (represent (univ (f % a)) (Op a) (f % a)))
  (universalElement . univ)


idAdj :: Category k => Adjunction k k (Id k) (Id k)
idAdj = mkAdjunction Id Id (\x -> x) (\x -> x)

composeAdj :: Adjunction d e f g -> Adjunction c d f' g' -> Adjunction c e (f' :.: f) (g :.: g')
composeAdj (Adjunction f g u c) (Adjunction f' g' u' c') = Adjunction (f' :.: f) (g :.: g')
  (compAssoc (g :.: g') f' f . precompose f % (compAssocInv g g' f' . postcompose g % u' . idPrecompInv g) . u)
  (c' . precompose g' % (idPrecomp f' . postcompose f' % c . compAssoc f' f g) . compAssocInv (f' :.: f) g g')


data AdjArrow c d where
  AdjArrow :: (Category c, Category d) => Adjunction c d f g -> AdjArrow (CatW c) (CatW d)

-- | The category with categories as objects and adjunctions as arrows.
instance Category AdjArrow where

  src (AdjArrow (Adjunction _ _ _ _)) = AdjArrow idAdj
  tgt (AdjArrow (Adjunction _ _ _ _)) = AdjArrow idAdj

  AdjArrow x . AdjArrow y = AdjArrow (composeAdj x y)



precomposeAdj :: Category e => Adjunction c d f g -> Adjunction (Nat c e) (Nat d e) (Precompose g e) (Precompose f e)
precomposeAdj (Adjunction f g un coun) = mkAdjunction
  (precompose g)
  (precompose f)
  (\nh@(Nat h _ _) -> compAssocInv h g f . (nh `o` un) . idPrecompInv h)
  (\nh@(Nat h _ _) -> idPrecomp h . (nh `o` coun) . compAssoc h f g)

postcomposeAdj :: Category e => Adjunction c d f g -> Adjunction (Nat e c) (Nat e d) (Postcompose f e) (Postcompose g e)
postcomposeAdj (Adjunction f g un coun) = mkAdjunction
  (postcompose f)
  (postcompose g)
  (\nh@(Nat h _ _) -> compAssoc g f h . (un `o` nh) . idPostcompInv h)
  (\nh@(Nat h _ _) -> idPostcomp h . (coun `o` nh) . compAssocInv f g h)

contAdj :: Adjunction (Op (->)) (->) (Opposite ((->) :-*: r) :.: OpOpInv (->)) ((->) :-*: r)
contAdj = mkAdjunction
  (Opposite (hom_X (\x -> x)) :.: OpOpInv)
  (hom_X (\x -> x))
  (\_ x f -> f x)
  (\_ -> Op (\x f -> f x))
