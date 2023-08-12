{-# LANGUAGE RankNTypes, GeneralizedNewtypeDeriving, TypeFamilies, TypeOperators, UndecidableInstances, GADTs, FlexibleContexts, NoImplicitPrelude #-}
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

import Data.Kind (Type)

import Data.Category
import Data.Category.Functor

import Data.Category.NaturalTransformation
import Data.Category.Product
import Data.Category.Unit


data I1 a
data I2 a

data (:++:) :: (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type where
  I1 :: c1 a1 b1 -> (:++:) c1 c2 (I1 a1) (I1 b1)
  I2 :: c2 a2 b2 -> (:++:) c1 c2 (I2 a2) (I2 b2)

-- | The coproduct category of categories @c1@ and @c2@.
instance (Category c1, Category c2) => Category (c1 :++: c2) where

  src (I1 a)      = I1 (src a)
  src (I2 a)      = I2 (src a)
  tgt (I1 a)      = I1 (tgt a)
  tgt (I2 a)      = I2 (tgt a)

  (I1 a) . (I1 b) = I1 (a . b)
  (I2 a) . (I2 b) = I2 (a . b)




data Inj1 (c1 :: Type -> Type -> Type) (c2 :: Type -> Type -> Type) = Inj1
-- | 'Inj1' is a functor which injects into the left category.
instance (Category c1, Category c2) => Functor (Inj1 c1 c2) where
  type Dom (Inj1 c1 c2) = c1
  type Cod (Inj1 c1 c2) = c1 :++: c2
  type Inj1 c1 c2 :% a = I1 a
  Inj1 % f = I1 f

data Inj2 (c1 :: Type -> Type -> Type) (c2 :: Type -> Type -> Type) = Inj2
-- | 'Inj2' is a functor which injects into the right category.
instance (Category c1, Category c2) => Functor (Inj2 c1 c2) where
  type Dom (Inj2 c1 c2) = c2
  type Cod (Inj2 c1 c2) = c1 :++: c2
  type Inj2 c1 c2 :% a = I2 a
  Inj2 % f = I2 f

data f1 :+++: f2 = f1 :+++: f2
-- | @f1 :+++: f2@ is the coproduct of the functors @f1@ and @f2@.
instance (Functor f1, Functor f2) => Functor (f1 :+++: f2) where
  type Dom (f1 :+++: f2) = Dom f1 :++: Dom f2
  type Cod (f1 :+++: f2) = Cod f1 :++: Cod f2
  type (f1 :+++: f2) :% (I1 a) = I1 (f1 :% a)
  type (f1 :+++: f2) :% (I2 a) = I2 (f2 :% a)
  (g :+++: _) % I1 f = I1 (g % f)
  (_ :+++: g) % I2 f = I2 (g % f)

data CodiagCoprod (k :: Type -> Type -> Type) = CodiagCoprod
-- | 'CodiagCoprod' is the codiagonal functor for coproducts.
instance Category k => Functor (CodiagCoprod k) where
  type Dom (CodiagCoprod k) = k :++: k
  type Cod (CodiagCoprod k) = k
  type CodiagCoprod k :% I1 a = a
  type CodiagCoprod k :% I2 a = a
  CodiagCoprod % I1 f = f
  CodiagCoprod % I2 f = f

newtype Cotuple1 (c1 :: Type -> Type -> Type) (c2 :: Type -> Type -> Type) a = Cotuple1 (Obj c1 a)
-- | 'Cotuple1' projects out to the left category, replacing a value from the right category with a fixed object.
instance (Category c1, Category c2) => Functor (Cotuple1 c1 c2 a1) where
  type Dom (Cotuple1 c1 c2 a1) = c1 :++: c2
  type Cod (Cotuple1 c1 c2 a1) = c1
  type Cotuple1 c1 c2 a1 :% I1 a = a
  type Cotuple1 c1 c2 a1 :% I2 a = a1
  Cotuple1 _ % I1 f = f
  Cotuple1 a % I2 _ = a

newtype Cotuple2 (c1 :: Type -> Type -> Type) (c2 :: Type -> Type -> Type) a = Cotuple2 (Obj c2 a)
-- | 'Cotuple2' projects out to the right category, replacing a value from the left category with a fixed object.
instance (Category c1, Category c2) => Functor (Cotuple2 c1 c2 a2) where
  type Dom (Cotuple2 c1 c2 a2) = c1 :++: c2
  type Cod (Cotuple2 c1 c2 a2) = c2
  type Cotuple2 c1 c2 a2 :% I1 a = a2
  type Cotuple2 c1 c2 a2 :% I2 a = a
  Cotuple2 a % I1 _ = a
  Cotuple2 _ % I2 f = f


data Cograph c d p :: Type -> Type -> Type where
  I1A :: c a1 b1 -> Cograph c d p (I1 a1) (I1 b1)
  I2A :: d a2 b2 -> Cograph c d p (I2 a2) (I2 b2)
  I12 :: Obj c a -> Obj d b -> p -> p :% (a, b) -> Cograph c d p (I1 a) (I2 b)

-- | The cograph of the profunctor @p@.
instance ProfunctorOf c d p => Category (Cograph c d p) where

  src (I1A a)       = I1A (src a)
  src (I2A a)       = I2A (src a)
  src (I12 a _ _ _) = I1A a
  tgt (I1A a)       = I1A (tgt a)
  tgt (I2A a)       = I2A (tgt a)
  tgt (I12 _ b _ _) = I2A b

  (I1A a) . (I1A b) = I1A (a . b)
  (I12 _ b p ab) . (I1A a) = I12 (src a) b p ((p % (Op a :**: b)) ab)
  (I2A b) . (I12 a _ p ab) = I12 a (tgt b) p ((p % (Op a :**: b)) ab)
  (I2A a) . (I2A b) = I2A (a . b)

-- | The cograph is a cotabulator with this 2-cell.
--
-- > C-Inj1-CG
-- > |   v   |
-- > p---@   |
-- > |   v   |
-- > D-Inj2-CG
isCotabulator :: Obj c a -> Obj d b -> p -> p :% (a, b) -> Cograph c d p (Inj1 c d :% a) (Inj2 c d :% b)
isCotabulator = I12

-- | Any 2-cell of shape p(a, b) -> e(f a, g b) factors through the cotabulator 2-cell.
--
-- > C--f--E    C-Inj1-CG--X--E
-- > |  v  |    |   v   |  v  |
-- > p--@  | == p---@   |  |  |
-- > |  v  |    |   v   |  v  |
-- > D--g--E    D-Inj2-CG--X--E
data CotabulatorFactorizer (c :: Type -> Type -> Type) (d :: Type -> Type -> Type) (e :: Type -> Type -> Type) p f g
  = CotabulatorFactorizer f g (forall a b. Obj c a -> Obj d b -> p :% (a, b) -> e (f :% a) (g :% b))
instance (ProfunctorOf c d p, FunctorOf c e f, FunctorOf d e g) => Functor (CotabulatorFactorizer c d e p f g) where
  type Dom (CotabulatorFactorizer c d e p f g) = Cograph c d p
  type Cod (CotabulatorFactorizer c d e p f g) = e
  type CotabulatorFactorizer c d e p f g :% I1 a = f :% a
  type CotabulatorFactorizer c d e p f g :% I2 a = g :% a
  CotabulatorFactorizer f _ _ % I1A a = f % a
  CotabulatorFactorizer _ g _ % I2A a = g % a
  CotabulatorFactorizer _ _ p2fg % I12 a b _ pab = p2fg a b pab

-- | The directed coproduct category of categories @c1@ and @c2@.
newtype (c1 :>>: c2) a b = DC (Cograph c1 c2 (Const (Op c1 :**: c2) (->) ()) a b) deriving Category


newtype NatAsFunctor f g = NatAsFunctor (Nat (Dom f) (Cod f) f g)

-- | A natural transformation @Nat c d@ is isomorphic to a functor from @c :**: 2@ to @d@.
instance (Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g) => Functor (NatAsFunctor f g) where

  type Dom (NatAsFunctor f g) = Dom f :**: Cograph Unit Unit (Hom Unit)
  type Cod (NatAsFunctor f g) = Cod f
  type NatAsFunctor f g :% (a, I1 ()) = f :% a
  type NatAsFunctor f g :% (a, I2 ()) = g :% a

  NatAsFunctor (Nat f _ _) % (a :**: I1A Unit) = f % a
  NatAsFunctor (Nat _ g _) % (a :**: I2A Unit) = g % a
  NatAsFunctor n           % (a :**: I12 Unit Unit Hom Unit) = n ! a
