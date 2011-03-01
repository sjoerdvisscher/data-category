{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleContexts, ScopedTypeVariables, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Adjunction
-- Copyright   :  (c) Sjoerd Visscher 2010
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
  , AdjArrow(..)
  
  -- * Adjunctions from universal morphisms
  , initialPropAdjunction
  , terminalPropAdjunction
  
  -- * Universal morphisms from adjunctions
  , adjunctionInitialProp
  , adjunctionTerminalProp
  
  -- * Examples
  , contAdj
  
) where
  
import Prelude (($), id, flip)
import Control.Monad.Instances ()

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation

data Adjunction c d f g = (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => Adjunction
  { leftAdjoint  :: f
  , rightAdjoint :: g
  , unit         :: Nat d d (Id d) (g :.: f)
  , counit       :: Nat c c (f :.: g) (Id c)
  }

mkAdjunction :: (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g 
  -> (forall a. Obj d a -> Component (Id d) (g :.: f) a) 
  -> (forall a. Obj c a -> Component (f :.: g) (Id c) a)
  -> Adjunction c d f g
mkAdjunction f g un coun = Adjunction f g (Nat Id (g :.: f) un) (Nat (f :.: g) Id coun)

leftAdjunct :: Adjunction c d f g -> Obj d a -> c (f :% a) b -> d a (g :% b)
leftAdjunct (Adjunction _ g un _) i h = (g % h) . (un ! i)
rightAdjunct :: Adjunction c d f g -> Obj c b -> d a (g :% b) -> c (f :% a) b
rightAdjunct (Adjunction f _ _ coun) i h = (coun ! i) . (f % h)

-- Each pair (FY, unit_Y) is an initial morphism from Y to G.
adjunctionInitialProp :: Adjunction c d f g -> Obj d y -> InitialUniversal y g (f :% y)
adjunctionInitialProp adj@(Adjunction f g un _) y = initialUniversal g (f % y) (un ! y) (rightAdjunct adj)

-- Each pair (GX, counit_X) is a terminal morphism from F to X.
adjunctionTerminalProp :: Adjunction c d f g -> Obj c x -> TerminalUniversal x f (g :% x)
adjunctionTerminalProp adj@(Adjunction f g _ coun) x = terminalUniversal f (g % x) (coun ! x) (leftAdjunct adj)



initialPropAdjunction :: forall f g c d. (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall y. Obj d y -> InitialUniversal y g (f :% y)) -> Adjunction c d f g
initialPropAdjunction f g univ = mkAdjunction f g un coun
  where
    coun :: forall a. Obj c a -> c (f :% (g :% a)) a
    coun a = represent (univ (g % a)) a (g % a)
    un   :: forall a. Obj d a -> d a (g :% (f :% a))
    un   a = universalElement (univ a)
   
terminalPropAdjunction :: forall f g c d. (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall x. Obj c x -> TerminalUniversal x f (g :% x)) -> Adjunction c d f g
terminalPropAdjunction f g univ = mkAdjunction f g un coun
  where
    un   :: forall a. Obj d a -> d a (g :% (f :% a))
    un   a = unOp $ represent (univ (f % a)) (Op a) (f % a)
    coun :: forall a. Obj c a -> c (f :% (g :% a)) a
    coun a = universalElement (univ a)
    

data AdjArrow c d where
  AdjArrow :: (Category c, Category d) => Adjunction c d f g -> AdjArrow (CatW c) (CatW d)

-- | The category with categories as objects and adjunctions as arrows.
instance Category AdjArrow where
  
  src (AdjArrow (Adjunction _ _ _ _)) = AdjArrow $ mkAdjunction Id Id id id
  tgt (AdjArrow (Adjunction _ _ _ _)) = AdjArrow $ mkAdjunction Id Id id id
  
  AdjArrow (Adjunction f g u c) . AdjArrow (Adjunction f' g' u' c') = AdjArrow $ 
    mkAdjunction (f' :.: f) (g :.: g') (\i -> ((Wrap g f % u') ! i) . (u ! i)) (\i -> (c' ! i) . ((Wrap f' g' % c) ! i))



data Cont1 r = Cont1
type instance Dom (Cont1 r) = (->)
type instance Cod (Cont1 r) = Op (->)
type instance (Cont1 r) :% a = a -> r
instance Functor (Cont1 r) where 
  Cont1 % f = Op (. f)

data Cont2 r = Cont2
type instance Dom (Cont2 r) = Op (->)
type instance Cod (Cont2 r) = (->)
type instance (Cont2 r) :% a = a -> r
instance Functor (Cont2 r) where 
  Cont2 % (Op f) = (. f)

contAdj :: Adjunction (Op (->)) (->) (Cont1 r) (Cont2 r)
contAdj = mkAdjunction Cont1 Cont2 (\_ -> flip ($)) (\_ -> Op (flip ($)))

-- leftAdjunct contAdj id . Op === unOp . rightAdjunct contAdj (Op id) === flip
