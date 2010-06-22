{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, FlexibleInstances, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Dialg
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Dialg(F,G), the category of (F,G)-dialgebras and (F,G)-homomorphisms.
-----------------------------------------------------------------------------
module Data.Category.Dialg where

import Prelude hiding ((.), id, Functor)
import qualified Prelude

import Data.Category
import Data.Category.Functor
import Data.Category.Limit
import Data.Category.Product


-- | Objects of Dialg(F,G) are (F,G)-dialgebras.
type Dialgebra f g a = Obj (Dialg f g) a

-- | Arrows of Dialg(F,G) are (F,G)-homomorphisms.
data Dialg f g a b where
  DialgA :: (Category c, Category d, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Functor f, Functor g) 
    => Dialgebra f g a -> Dialgebra f g b -> c a b -> Dialg f g a b


instance Category (Dialg f g) where
  
  data Obj (Dialg f g) a where
    Dialgebra :: (Category c, Category d, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Functor f, Functor g) 
      => Obj c a -> d (F f a) (F g a) -> Obj (Dialg f g) a
      
  src (DialgA s _ _) = s
  tgt (DialgA _ t _) = t
  
  id x@(Dialgebra a _)        = DialgA x x $ id a
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




-- | 'FixF' provides the initial F-algebra for endofunctors in Hask.
newtype FixF f = InF { outF :: f (FixF f) }

-- | Catamorphisms for endofunctors in Hask.
cataHask :: Prelude.Functor f => Cata (EndoHask f) a
cataHask a@(Dialgebra HaskO f) = DialgA initialObject a $ cata f where cata f = f . fmap (cata f) . outF 

-- -- | Anamorphisms for endofunctors in Hask.
anaHask :: Prelude.Functor f => Ana (EndoHask f) a
anaHask a@(Dialgebra HaskO f) = DialgA a terminalObject $ ana f where ana f = InF . fmap (ana f) . f 


instance Prelude.Functor f => HasInitialObject (Dialg (EndoHask f) (Id (->))) where
  
  type InitialObject (Dialg (EndoHask f) (Id (->))) = FixF f
  
  initialObject = Dialgebra HaskO InF
  initialize = cataHask
  
instance  Prelude.Functor f => HasTerminalObject (Dialg (Id (->)) (EndoHask f)) where

  type TerminalObject (Dialg (Id (->)) (EndoHask f)) = FixF f
  
  terminalObject = Dialgebra HaskO outF
  terminate = anaHask
  


-- | The category for defining the natural numbers and primitive recursion can be described as
-- @Dialg(F,G)@, with @F(A)=\<1,A>@ and @G(A)=\<A,A>@.
data NatF ((~>) :: * -> * -> *) where
  NatF :: HasTerminalObject (~>) => NatF (~>)
type instance Dom (NatF (~>)) = (~>)
type instance Cod (NatF (~>)) = (~>) :*: (~>)
type instance F (NatF (~>)) a = (TerminalObject (~>),  a)
instance Functor (NatF (~>)) where
  NatF %% x = ProdO terminalObject x
  NatF %  f = id terminalObject :**: f

data NatNum = Z | S NatNum
primRec :: t -> (t -> t) -> NatNum -> t
primRec z _ Z     = z
primRec z s (S n) = s (primRec z s n)

instance HasInitialObject (Dialg (NatF (->)) (DiagProd (->))) where
  
  type InitialObject (Dialg (NatF (->)) (DiagProd (->))) = NatNum
    
  initialObject = Dialgebra HaskO (const Z :**: S)
  
  initialize o@(Dialgebra HaskO p) = DialgA initialObject o $ f p where
    f :: ((->) :*: (->)) ((), t) (t, t) -> NatNum -> t
    f (z :**: s) = primRec (z ()) s
    