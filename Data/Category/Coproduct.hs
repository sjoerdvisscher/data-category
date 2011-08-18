{-# LANGUAGE TypeFamilies, TypeOperators, GADTs, FlexibleContexts, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Coproduct
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Coproduct where

import Data.Category
import Data.Category.Functor


data I1 a
data I2 a

data (:++:) :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  I1 :: c1 a1 b1 -> (:++:) c1 c2 (I1 a1) (I1 b1)
  I2 :: c2 a2 b2 -> (:++:) c1 c2 (I2 a2) (I2 b2)

-- | The coproduct category of category @c1@ and @c2@.
instance (Category c1, Category c2) => Category (c1 :++: c2) where
  
  src (I1 a)      = I1 (src a)
  src (I2 a)      = I2 (src a)
  tgt (I1 a)      = I1 (tgt a)
  tgt (I2 a)      = I2 (tgt a)

  (I1 a) . (I1 b) = I1 (a . b)
  (I2 a) . (I2 b) = I2 (a . b)

  
  
    
data Inj1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Inj1
type instance Dom (Inj1 c1 c2) = c1
type instance Cod (Inj1 c1 c2) = c1 :++: c2
type instance Inj1 c1 c2 :% a = I1 a
-- | 'Inj1' is a functor which injects into the left category.
instance (Category c1, Category c2) => Functor (Inj1 c1 c2) where 
  Inj1 % f = I1 f

data Inj2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Inj2
type instance Dom (Inj2 c1 c2) = c2
type instance Cod (Inj2 c1 c2) = c1 :++: c2
type instance Inj2 c1 c2 :% a = I2 a
-- | 'Inj2' is a functor which injects into the right category.
instance (Category c1, Category c2) => Functor (Inj2 c1 c2) where 
  Inj2 % f = I2 f

data f1 :+++: f2 = f1 :+++: f2
type instance Dom (f1 :+++: f2) = Dom f1 :++: Dom f2
type instance Cod (f1 :+++: f2) = Cod f1 :++: Cod f2
type instance (f1 :+++: f2) :% (I1 a) = I1 (f1 :% a)
type instance (f1 :+++: f2) :% (I2 a) = I2 (f2 :% a)
-- | @f1 :+++: f2@ is the coproduct of the functors @f1@ and @f2@.
instance (Functor f1, Functor f2) => Functor (f1 :+++: f2) where 
  (g :+++: _) % I1 f = I1 (g % f)
  (_ :+++: g) % I2 f = I2 (g % f)
  
data CodiagCoprod ((~>) :: * -> * -> *) = CodiagCoprod
type instance Dom (CodiagCoprod (~>)) = (~>) :++: (~>)
type instance Cod (CodiagCoprod (~>)) = (~>)
type instance CodiagCoprod (~>) :% I1 a = a
type instance CodiagCoprod (~>) :% I2 a = a
-- | 'CodiagCoprod' is the codiagonal functor for coproducts.
instance Category (~>) => Functor (CodiagCoprod (~>)) where 
  CodiagCoprod % I1 f = f
  CodiagCoprod % I2 f = f

data Cotuple1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) a = Cotuple1 (Obj c1 a)
type instance Dom (Cotuple1 c1 c2 a1) = c1 :++: c2
type instance Cod (Cotuple1 c1 c2 a1) = c1
type instance Cotuple1 c1 c2 _1 :% I1 a1 = a1
type instance Cotuple1 c1 c2 a1 :% I2 a2 = a1
-- | 'Cotuple1' projects out to the left category, replacing a value from the right category with a fixed object.
instance (Category c1, Category c2) => Functor (Cotuple1 c1 c2 a1) where
  Cotuple1 _ % I1 f = f
  Cotuple1 a % I2 _ = a

data Cotuple2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) a = Cotuple2 (Obj c2 a)
type instance Dom (Cotuple2 c1 c2 a2) = c1 :++: c2
type instance Cod (Cotuple2 c1 c2 a2) = c2
type instance Cotuple2 c1 c2 a2 :% I1 a1 = a2
type instance Cotuple2 c1 c2 _2 :% I2 a2 = a2
-- | 'Cotuple2' projects out to the right category, replacing a value from the left category with a fixed object.
instance (Category c1, Category c2) => Functor (Cotuple2 c1 c2 a2) where
  Cotuple2 a % I1 _ = a
  Cotuple2 _ % I2 f = f

