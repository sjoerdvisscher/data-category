{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts, ViewPatterns, ScopedTypeVariables, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Dialg
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Dialg(F,G), the category of (F,G)-dialgebras and (F,G)-homomorphisms.
-----------------------------------------------------------------------------
module Data.Category.Dialg where

import Prelude (($), id)
import qualified Prelude

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit
import Data.Category.Product
import Data.Category.Monoidal
import qualified Data.Category.Adjunction as A


-- | Objects of Dialg(F,G) are (F,G)-dialgebras.
data Dialgebra f g a where
  Dialgebra :: (Category c, Category d, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Functor f, Functor g) 
    => Obj c a -> d (f :% a) (g :% a) -> Dialgebra f g a

-- | Arrows of Dialg(F,G) are (F,G)-homomorphisms.
data Dialg f g a b where
  DialgA :: (Category c, Category d, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Functor f, Functor g) 
    => Dialgebra f g a -> Dialgebra f g b -> c a b -> Dialg f g a b

dialgId :: Dialgebra f g a -> Obj (Dialg f g) a
dialgId d@(Dialgebra a _) = DialgA d d a

dialgebra :: Obj (Dialg f g) a -> Dialgebra f g a
dialgebra (DialgA d _ _) = d

-- | The category of (F,G)-dialgebras.
instance Category (Dialg f g) where
  
  src (DialgA s _ _) = dialgId s
  tgt (DialgA _ t _) = dialgId t
  
  DialgA _ t f . DialgA s _ g = DialgA s t $ f . g



type Alg f = Dialg f (Id (Dom f))
type Algebra f a = Dialgebra f (Id (Dom f)) a
type Coalg f = Dialg (Id (Dom f)) f
type Coalgebra f a = Dialgebra (Id (Dom f)) f a

-- | The initial F-algebra is the initial object in the category of F-algebras.
type InitialFAlgebra f = InitialObject (Alg f)

-- | The terminal F-coalgebra is the terminal object in the category of F-coalgebras.
type TerminalFAlgebra f = TerminalObject (Coalg f)

-- | A catamorphism of an F-algebra is the arrow to it from the initial F-algebra.
type Cata f a = Algebra f a -> Alg f (InitialFAlgebra f) a

-- | A anamorphism of an F-coalgebra is the arrow from it to the terminal F-coalgebra.
type Ana f a = Coalgebra f a -> Coalg f a (TerminalFAlgebra f)




newtype FixF f = InF { outF :: f :% FixF f }

-- | Catamorphisms for endofunctors in Hask.
cataHask :: Prelude.Functor f => Cata (EndoHask f) a
cataHask a@(Dialgebra _ f) = DialgA (dialgebra initialObject) a $ cata_f where cata_f = f . (EndoHask % cata_f) . outF 

-- | Anamorphisms for endofunctors in Hask.
anaHask :: Prelude.Functor f => Ana (EndoHask f) a
anaHask a@(Dialgebra _ f) = DialgA a (dialgebra terminalObject) $ ana_f where ana_f = InF . (EndoHask % ana_f) . f 


-- | 'FixF' provides the initial F-algebra for endofunctors in Hask.
instance Prelude.Functor f => HasInitialObject (Dialg (EndoHask f) (Id (->))) where
  
  type InitialObject (Dialg (EndoHask f) (Id (->))) = FixF (EndoHask f)
  
  initialObject = dialgId $ Dialgebra id InF
  initialize a = cataHask (dialgebra a)
  
-- | 'FixF' also provides the terminal F-coalgebra for endofunctors in Hask.
instance Prelude.Functor f => HasTerminalObject (Dialg (Id (->)) (EndoHask f)) where

  type TerminalObject (Dialg (Id (->)) (EndoHask f)) = FixF (EndoHask f)
  
  terminalObject = dialgId $ Dialgebra id outF
  terminate a = anaHask (dialgebra a)
  


data NatNum = Z () | S NatNum
primRec :: (() -> t) -> (t -> t) -> NatNum -> t
primRec z _ (Z ()) = z ()
primRec z s (S  n) = s (primRec z s n)

-- | The category for defining the natural numbers and primitive recursion can be described as
-- @Dialg(F,G)@, with @F(A)=\<1,A>@ and @G(A)=\<A,A>@.
instance HasInitialObject (Dialg (Tuple1 (->) (->) ()) (DiagProd (->))) where
  
  type InitialObject (Dialg (Tuple1 (->) (->) ()) (DiagProd (->))) = NatNum
    
  initialObject = dialgId $ Dialgebra id (Z :**: S)
  
  initialize (dialgebra -> d@(Dialgebra _ (z :**: s))) = DialgA (dialgebra initialObject) d $ primRec z s



data FreeAlg m = FreeAlg (Monad m)
type instance Dom (FreeAlg m) = Dom m
type instance Cod (FreeAlg m) = Alg m
type instance FreeAlg m :% a = m :% a
-- | @FreeAlg@ M takes @x@ to the free algebra @(M x, mu_x)@ of the monad @M@.
instance (Functor m, Dom m ~ (~>), Cod m ~ (~>)) => Functor (FreeAlg m) where
  FreeAlg m % f = DialgA (alg (src f)) (alg (tgt f)) $ monadFunctor m % f
    where
      alg :: Obj (~>) x -> Algebra m (m :% x)
      alg x = Dialgebra (monadFunctor m % x) (multiply m ! x)

data ForgetAlg m = ForgetAlg
type instance Dom (ForgetAlg m) = Alg m
type instance Cod (ForgetAlg m) = Dom m
type instance ForgetAlg m :% a = a
-- | @ForgetAlg m@ is the forgetful functor for @Alg m@.
instance (Functor m, Dom m ~ (~>), Cod m ~ (~>)) => Functor (ForgetAlg m) where
  ForgetAlg % DialgA _ _ f = f

eilenbergMooreAdj :: (Functor m, Dom m ~ (~>), Cod m ~ (~>)) 
  => Monad m -> A.Adjunction (Alg m) (~>) (FreeAlg m) (ForgetAlg m)
eilenbergMooreAdj m = A.mkAdjunction (FreeAlg m) ForgetAlg
  (\x -> unit m ! x)
  (\(DialgA (Dialgebra _ h) _ _) -> DialgA (Dialgebra (src h) (monadFunctor m % h)) (Dialgebra (tgt h) h) h)
