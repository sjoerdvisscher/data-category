{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Alg
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Alg(F), the category of F-algebras and F-homomorphisms.
-----------------------------------------------------------------------------
module Data.Category.Alg where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Void
import Data.Category.Hask

-- | Objects of Alg(F) are F-algebras.
newtype Algebra f a = Algebra (Dom f (F f a) a)

-- | Arrows of Alg(F) are F-homomorphisms.
data family Alg f a b :: *
data instance Alg f (Algebra f a) (Algebra f b) = AlgA (Dom f a b)

newtype instance Nat (Alg f) d g h = 
  AlgNat { unAlgNat :: forall a. Obj (Algebra f a) -> Component g h (Algebra f a) }

instance (Dom f ~ (~>), Cod f ~ (~>), CategoryO (~>) a) => CategoryO (Alg f) (Algebra f a) where
  id = AlgA id
  (!) = unAlgNat
instance (Dom f ~ (~>), Cod f ~ (~>), CategoryA (~>) a b c) => CategoryA (Alg f) (Algebra f a) (Algebra f b) (Algebra f c) where
  AlgA f . AlgA g = AlgA (f . g)

-- | The initial F-algebra is the initial object in the category of F-algebras.
type InitialFAlgebra f = InitialObject (Alg f)

-- | A catamorphism of an F-algebra is the arrow to it from the initial F-algebra.
type Cata f a = Algebra f a -> Alg f (InitialFAlgebra f) (Algebra f a)

-- | FixF provides the initial F-algebra for endofunctors in Hask.
newtype FixF f = InF { outF :: f (FixF f) }

-- | Catamorphisms for endofunctors in Hask.
cataHask :: Functor f => Cata (EndoHask f) a
cataHask (Algebra f) = AlgA $ cata f where cata f = f . fmap (cata f) . outF 

instance Functor f => VoidColimit (Alg (EndoHask f)) where
  type InitialObject (Alg (EndoHask f)) = Algebra (EndoHask f) (FixF f)
  voidColimit = InitialUniversal VoidNat (AlgNat $ \f VoidNat -> cataHask f)