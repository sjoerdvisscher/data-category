{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, FlexibleInstances, UndecidableInstances, GADTs, RankNTypes, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Functor
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Functor (

  -- * Cat
    Cat(..)
  , CatW

  -- * Functors
  , Functor(..)

  -- ** Functor instances
  , Id(..)
  , (:.:)(..)
  , Const(..), ConstF
  , Opposite(..)
  , OpOp(..)
  , OpOpInv(..)

  -- *** Related to the product category
  , Proj1(..)
  , Proj2(..)
  , (:***:)(..)
  , DiagProd(..)
  , Tuple1, tuple1
  , Tuple2, tuple2
  , Swap, swap

  -- *** Hom functors
  , Hom(..)
  , (:*-:), homX_
  , (:-*:), hom_X
  , HomF, homF
  , Star, star
  , Costar, costar

) where

import Data.Category
import Data.Category.Product

infixr 9 %
infixr 9 :%



-- | Functors map objects and arrows.
class (Category (Dom ftag), Category (Cod ftag)) => Functor ftag where

  -- | The domain, or source category, of the functor.
  type Dom ftag :: * -> * -> *
  -- | The codomain, or target category, of the functor.
  type Cod ftag :: * -> * -> *

  -- | @:%@ maps objects.
  type ftag :% a :: *

  -- | @%@ maps arrows.
  (%)  :: ftag -> Dom ftag a b -> Cod ftag (ftag :% a) (ftag :% b)




-- | Functors are arrows in the category Cat.
data Cat :: * -> * -> * where
  CatA :: (Functor ftag, Category (Dom ftag), Category (Cod ftag)) => ftag -> Cat (CatW (Dom ftag)) (CatW (Cod ftag))

-- | We need a wrapper here because objects need to be of kind *, and categories are of kind * -> * -> *.
data CatW :: (* -> * -> *) -> *


-- | @Cat@ is the category with categories as objects and funtors as arrows.
instance Category Cat where

  src (CatA _)      = CatA Id
  tgt (CatA _)      = CatA Id

  CatA f1 . CatA f2 = CatA (f1 :.: f2)



data Id (k :: * -> * -> *) = Id

-- | The identity functor on k
instance Category k => Functor (Id k) where
  type Dom (Id k) = k
  type Cod (Id k) = k
  type Id k :% a = a

  _ % f = f


data (g :.: h) where
  (:.:) :: (Functor g, Functor h, Cod h ~ Dom g) => g -> h -> g :.: h

-- | The composition of two functors.
instance (Category (Cod g), Category (Dom h)) => Functor (g :.: h) where
  type Dom (g :.: h) = Dom h
  type Cod (g :.: h) = Cod g
  type (g :.: h) :% a = g :% (h :% a)

  (g :.: h) % f = g % (h % f)



data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x where
  Const :: Obj c2 x -> Const c1 c2 x

-- | The constant functor.
instance (Category c1, Category c2) => Functor (Const c1 c2 x) where
  type Dom (Const c1 c2 x) = c1
  type Cod (Const c1 c2 x) = c2
  type Const c1 c2 x :% a = x

  Const x % _ = x

-- | The constant functor with the same domain and codomain as f.
type ConstF f = Const (Dom f) (Cod f)


data Opposite f where
  Opposite :: Functor f => f -> Opposite f

-- | The dual of a functor
instance (Category (Dom f), Category (Cod f)) => Functor (Opposite f) where
  type Dom (Opposite f) = Op (Dom f)
  type Cod (Opposite f) = Op (Cod f)
  type Opposite f :% a = f :% a

  Opposite f % Op a = Op (f % a)


data OpOp (k :: * -> * -> *) = OpOp

-- | The @Op (Op x) = x@ functor.
instance Category k => Functor (OpOp k) where
  type Dom (OpOp k) = Op (Op k)
  type Cod (OpOp k) = k
  type OpOp k :% a = a

  OpOp % Op (Op f) = f


data OpOpInv (k :: * -> * -> *) = OpOpInv

-- | The @x = Op (Op x)@ functor.
instance Category k => Functor (OpOpInv k) where
  type Dom (OpOpInv k) = k
  type Cod (OpOpInv k) = Op (Op k)
  type OpOpInv k :% a = a

  OpOpInv % f = Op (Op f)


data Proj1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Proj1

-- | 'Proj1' is a bifunctor that projects out the first component of a product.
instance (Category c1, Category c2) => Functor (Proj1 c1 c2) where
  type Dom (Proj1 c1 c2) = c1 :**: c2
  type Cod (Proj1 c1 c2) = c1
  type Proj1 c1 c2 :% (a1, a2) = a1

  Proj1 % (f1 :**: _) = f1


data Proj2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Proj2

-- | 'Proj2' is a bifunctor that projects out the second component of a product.
instance (Category c1, Category c2) => Functor (Proj2 c1 c2) where
  type Dom (Proj2 c1 c2) = c1 :**: c2
  type Cod (Proj2 c1 c2) = c2
  type Proj2 c1 c2 :% (a1, a2) = a2

  Proj2 % (_ :**: f2) = f2


data f1 :***: f2 = f1 :***: f2

-- | @f1 :***: f2@ is the product of the functors @f1@ and @f2@.
instance (Functor f1, Functor f2) => Functor (f1 :***: f2) where
  type Dom (f1 :***: f2) = Dom f1 :**: Dom f2
  type Cod (f1 :***: f2) = Cod f1 :**: Cod f2
  type (f1 :***: f2) :% (a1, a2) = (f1 :% a1, f2 :% a2)

  (g1 :***: g2) % (f1 :**: f2) = (g1 % f1) :**: (g2 % f2)


data DiagProd (k :: * -> * -> *) = DiagProd

-- | 'DiagProd' is the diagonal functor for products.
instance Category k => Functor (DiagProd k) where
  type Dom (DiagProd k) = k
  type Cod (DiagProd k) = k :**: k
  type DiagProd k :% a = (a, a)

  DiagProd % f = f :**: f


type Tuple1 c1 c2 a = (Const c2 c1 a :***: Id c2) :.: DiagProd c2

-- | 'Tuple1' tuples with a fixed object on the left.
tuple1 :: (Category c1, Category c2) => Obj c1 a -> Tuple1 c1 c2 a
tuple1 a = (Const a :***: Id) :.: DiagProd

-- type Tuple2 c1 c2 a = (Id c1 :***: Const c1 c2 a) :.: DiagProd c1
--
-- -- | 'Tuple2' tuples with a fixed object on the right.
-- tuple2 :: (Category c1, Category c2) => Obj c2 a -> Tuple2 c1 c2 a
-- tuple2 a = (Id :***: Const a) :.: DiagProd

type Swap (c1 :: * -> * -> *) (c2 :: * -> * -> *) = (Proj2 c1 c2 :***: Proj1 c1 c2) :.: DiagProd (c1 :**: c2)
-- | 'swap' swaps the 2 categories of the product of categories.
swap :: (Category c1, Category c2) => Swap c1 c2
swap = (Proj2 :***: Proj1) :.: DiagProd

type Tuple2 c1 c2 a = Swap c2 c1 :.: Tuple1 c2 c1 a
-- | 'Tuple2' tuples with a fixed object on the right.
tuple2 :: (Category c1, Category c2) => Obj c2 a -> Tuple2 c1 c2 a
tuple2 a = swap :.: tuple1 a



data Hom (k :: * -> * -> *) = Hom

-- | The Hom functor, Hom(--,--), a bifunctor contravariant in its first argument and covariant in its second argument.
instance Category k => Functor (Hom k) where
  type Dom (Hom k) = Op k :**: k
  type Cod (Hom k) = (->)
  type (Hom k) :% (a1, a2) = k a1 a2

  Hom % (Op f1 :**: f2) = \g -> f2 . g . f1


type x :*-: k = Hom k :.: Tuple1 (Op k) k x
-- | The covariant functor Hom(X,--)
homX_ :: Category k => Obj k x -> x :*-: k
homX_ x = Hom :.: tuple1 (Op x)

type k :-*: x = Hom k :.: Tuple2 (Op k) k x
-- | The contravariant functor Hom(--,X)
hom_X :: Category k => Obj k x -> k :-*: x
hom_X x = Hom :.: tuple2 x


type HomF f g = Hom (Cod f) :.: (Opposite f :***: g)
homF :: (Functor f, Functor g, Cod f ~ Cod g) => f -> g -> HomF f g
homF f g = Hom :.: (Opposite f :***: g)

type Star f = HomF (Id (Cod f)) f
star :: Functor f => f -> Star f
star f = homF Id f

type Costar f = HomF f (Id (Cod f))
costar :: Functor f => f -> Costar f
costar f = homF f Id
