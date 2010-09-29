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
  
  -- * Adjunctions from universal morphisms
  , initialPropAdjunction
  , terminalPropAdjunction
  
  -- * Adjunctions to universal morphisms
  , adjunctionInitialProp
  , adjunctionTerminalProp
  
  -- * Adjunctions as a category
  , AdjArrow(..)
  
  -- * (Co)limitfunctor adjunction
  , limitAdj
  , colimitAdj
  
  -- * (Co)monad of an adjunction
  , adjunctionMonad
  , adjunctionComonad
  
  -- * Examples
  -- ** The curry/uncurry adjunction
  , curryAdj
  , curry
  , uncurry
  , State
  , stateMonadReturn
  , stateMonadJoin
  , Context
  , contextComonadExtract
  , contextComonadDuplicate
  
  -- ** The continuation adjunction
  , contAdj
  
) where
  
import Prelude (($), id, flip, undefined)
import Control.Monad.Instances ()

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit
import qualified Data.Category.Monoidal as M

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
adjunctionInitialProp adj@(Adjunction f _ un _) y = InitialUniversal (f % y) (un ! y) (rightAdjunct adj)

-- Each pair (GX, counit_X) is a terminal morphism from F to X.
adjunctionTerminalProp :: Adjunction c d f g -> Obj c x -> TerminalUniversal x f (g :% x)
adjunctionTerminalProp adj@(Adjunction _ g _ coun) x = TerminalUniversal (g % x) (coun ! x) (leftAdjunct adj)



initialPropAdjunction :: (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall y. Obj d y -> InitialUniversal y g (f :% y)) -> Adjunction c d f g
initialPropAdjunction f g univ = mkAdjunction f g un coun
  where
    coun a = initialFactorizer (univ (g % a)) a (g % a)
    un   a = initialMorphism (univ a)
    
terminalPropAdjunction :: (Functor f, Functor g, Category c, Category d, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall x. Obj c x -> TerminalUniversal x f (g :% x)) -> Adjunction c d f g
terminalPropAdjunction f g univ = mkAdjunction f g un coun
  where
    un   a = terminalFactorizer (univ (f % a)) a (f % a)
    coun a = terminalMorphism (univ a)
    

data AdjArrow c d where
  AdjArrow :: (Category c, Category d) => Adjunction c d f g -> AdjArrow (CatW c) (CatW d)

-- | The category with categories as objects and adjunctions as arrows.
instance Category AdjArrow where
  
  src (AdjArrow (Adjunction _ _ _ _)) = AdjArrow $ mkAdjunction Id Id id id
  tgt (AdjArrow (Adjunction _ _ _ _)) = AdjArrow $ mkAdjunction Id Id id id
  
  AdjArrow (Adjunction f g u c) . AdjArrow (Adjunction f' g' u' c') = AdjArrow $ 
    mkAdjunction (f' :.: f) (g :.: g') 
      (\i -> ((Postcompose g % Precompose f % u') ! i) . (u ! i)) 
      (\i -> (c' ! i) . ((Postcompose f' % Precompose g' % c) ! i))


-- | The limit functor is right adjoint to the diagonal functor.
limitAdj :: forall j (~>). HasLimits j (~>) 
  => LimitFunctor j (~>) 
  -> Adjunction (Nat j (~>)) (~>) (Diag j (~>)) (LimitFunctor j (~>))
limitAdj LimitFunctor = terminalPropAdjunction Diag LimitFunctor univ
  where
    univ :: Obj (Nat j (~>)) f -> TerminalUniversal f (Diag j (~>)) (LimitFam j (~>) f)
    univ f@Nat{} = limitUniv f

-- | The colimit functor is left adjoint to the diagonal functor.
colimitAdj :: forall j (~>). HasColimits j (~>) 
  => ColimitFunctor j (~>) 
  -> Adjunction (~>) (Nat j (~>)) (ColimitFunctor j (~>)) (Diag j (~>))
colimitAdj ColimitFunctor = initialPropAdjunction ColimitFunctor Diag univ
  where
    univ :: Obj (Nat j (~>)) f -> InitialUniversal f (Diag j (~>)) (ColimitFam j (~>) f)
    univ f@Nat{} = colimitUniv f


adjunctionMonad :: Adjunction c d f g -> M.Monad (g :.: f)
adjunctionMonad (Adjunction f g un coun) = M.mkMonad (g :.: f) (un !) ((Postcompose g % Precompose f % coun) !)

adjunctionComonad :: Adjunction c d f g -> M.Comonad (f :.: g)
adjunctionComonad (Adjunction f g un coun) = M.mkComonad (f :.: g) (coun !) ((Postcompose f % Precompose g % un) !)


curryAdj :: Adjunction (->) (->) (EndoHask ((,) e)) (EndoHask ((->) e))
curryAdj = mkAdjunction EndoHask EndoHask (\_ -> \a e -> (e, a)) (\_ -> \(e, f) -> f e)

curry :: ((a, b) -> c) -> a -> b -> c
curry = flip . leftAdjunct curryAdj id

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry = rightAdjunct curryAdj id . flip

type State e a = e -> (e, a)

stateMonadReturn :: a -> State e a
stateMonadReturn = M.unit (adjunctionMonad curryAdj) ! id

stateMonadJoin :: State e (State e a) -> State e a
stateMonadJoin = M.multiply (adjunctionMonad curryAdj) ! id

type Context e a = (e, e -> a)

contextComonadExtract :: Context e a -> a
contextComonadExtract = M.counit (adjunctionComonad curryAdj) ! id

contextComonadDuplicate :: Context e a -> Context e (Context e a)
contextComonadDuplicate = M.comultiply (adjunctionComonad curryAdj) ! id


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
