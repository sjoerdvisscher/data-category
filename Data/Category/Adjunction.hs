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
module Data.Category.Adjunction where
  
import Prelude hiding ((.), id, Functor)
import Control.Monad.Instances()

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit

data Adjunction c d f g where
  Adjunction :: (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d) =>
    f -> g -> Nat d d (Id d) (g :.: f) -> Nat c c (f :.: g) (Id c) -> Adjunction c d f g

mkAdjunction :: (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g 
  -> (forall a. Obj d a -> Component (Id d) (g :.: f) a) 
  -> (forall a. Obj c a -> Component (f :.: g) (Id c) a)
  -> Adjunction c d f g
mkAdjunction f g un coun = Adjunction f g (Nat Id (g :.: f) un) (Nat (f :.: g) Id coun)

unit :: Adjunction c d f g -> Id d :~> (g :.: f)
unit (Adjunction _ _ u _) = u
counit :: Adjunction c d f g -> (f :.: g) :~> Id c
counit (Adjunction _ _ _ c) = c

leftAdjunct :: Adjunction c d f g -> Obj d a -> c (F f a) b -> d a (F g b)
leftAdjunct (Adjunction _ g un _) i h = (g % h) . (un ! i)
rightAdjunct :: Adjunction c d f g -> Obj c b -> d a (F g b) -> c (F f a) b
rightAdjunct (Adjunction f _ _ coun) i h = (coun ! i) . (f % h)

-- Each pair (FY, unit_Y) is an initial morphism from Y to G.
adjunctionInitialProp :: Adjunction c d f g -> Obj d y -> InitialUniversal y g (F f y)
adjunctionInitialProp adj@(Adjunction f _ un _) y = InitialUniversal (f %% y) (un ! y) (rightAdjunct adj)

-- Each pair (GX, counit_X) is a terminal morphism from F to X.
adjunctionTerminalProp :: Adjunction c d f g -> Obj c x -> TerminalUniversal x f (F g x)
adjunctionTerminalProp adj@(Adjunction _ g _ coun) x = TerminalUniversal (g %% x) (coun ! x) (leftAdjunct adj)


data AdjArrow c d where
  AdjArrow :: (Category c, Category d) => Adjunction c d f g -> AdjArrow (CatW c) (CatW d)

instance Category AdjArrow where
  
  data Obj AdjArrow a where
    AdjCategory :: Category (~>) => Obj AdjArrow (CatW (~>))
  
  src (AdjArrow _) = AdjCategory
  tgt (AdjArrow _) = AdjCategory
  
  id AdjCategory = AdjArrow $ mkAdjunction Id Id id id
  
  AdjArrow (Adjunction f g u c) . AdjArrow (Adjunction f' g' u' c') = AdjArrow $ 
    Adjunction (f' :.: f) (g :.: g') (wrap g f u' . u) (c' . cowrap f' g' c)


wrap :: (Functor g, Functor f, Dom g ~ Dom f', Dom g ~ Cod f) 
  => g -> f -> Nat (Dom f') (Dom f') (Id (Dom f')) (g' :.: f') -> (g :.: f) :~> ((g :.: g') :.: (f' :.: f))
wrap g f (Nat Id (g' :.: f') n) = Nat (g :.: f) ((g :.: g') :.: (f' :.: f)) $ (g %) . n . (f %%)

cowrap :: (Functor f', Functor g', Dom f' ~ Dom g, Dom f' ~ Cod g') 
  => f' -> g' -> Nat (Dom g) (Dom g) (f :.: g) (Id (Dom g)) -> ((f' :.: f) :.: (g :.: g')) :~> (f' :.: g')
cowrap f' g' (Nat (f :.: g) Id n) = Nat ((f' :.: f) :.: (g :.: g')) (f' :.: g') $ (f' %) . n . (g' %%)


curryAdj :: Adjunction (->) (->) (EndoHask ((,) e)) (EndoHask ((->) e))
curryAdj = mkAdjunction EndoHask EndoHask (\HaskO -> \a e -> (e, a)) (\HaskO -> \(e, f) -> f e)


data RightAdjoint :: * -> * -> * where
  RightAdjoint :: (Functor f, Dom f ~ d, Cod f ~ c, Category c, Category d) => 
    f -> (forall x. Obj c x -> TerminalUniversal x f (F g x)) -> RightAdjoint f g
  
type instance Dom (RightAdjoint f g) = Cod f
type instance Cod (RightAdjoint f g) = Dom f
type instance F (RightAdjoint f g) a = F g a

instance Functor (RightAdjoint f g) where
  RightAdjoint f univ %% x = tuObject (univ x)
  -- RightAdjoint f univ % h  = terminalFactorizer (univ $ src h) o m
  --   where
  --     targetUniv = univ $ tgt h
  --     o = tuObject targetUniv
  --     m = terminalMorphism targetUniv . h

terminalPropAdjunction :: RightAdjoint f g -> Adjunction (Cod f) (Dom f) f (RightAdjoint f g) 
terminalPropAdjunction g@(RightAdjoint f univ) = mkAdjunction f g 
  (\a -> let fa = f %% a in terminalFactorizer (univ fa) a (id fa))
  (terminalMorphism . univ)

-- limitAdj :: HasLimits j (~>) => Adjunction (Nat j (~>)) (~>) (Diag j (~>)) (RightAdjoint (Diag j (~>)) (LimitFunctor j (~>)))
-- limitAdj = terminalPropAdjunction (RightAdjoint Diag limitUniversal :: RightAdjoint (Diag j (~>)) (LimitFunctor j (~>)))