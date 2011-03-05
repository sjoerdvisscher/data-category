{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, FlexibleInstances, UndecidableInstances, GADTs, RankNTypes #-}
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
  , Dom
  , Cod
  , Functor(..)
  , (:%)
  
  -- ** Functor instances
  , Id(..)
  , (:.:)(..)
  , Const(..), ConstF
  , Opposite(..)
  , OpOp(..)
  , OpOpInv(..)
  , EndoHask(..)
  
  -- *** Related to the product category
  , Proj1(..)
  , Proj2(..)
  , (:***:)(..)
  , DiagProd(..)
  , Tuple1(..)
  , Tuple2(..)
  
  -- *** Hom functors
  , Hom(..)
  , (:*-:)
  , homX_
  , (:-*:)
  , hom_X
  
) where
  
import Prelude hiding ((.), Functor)
import qualified Prelude
  
import Data.Category
import Data.Category.Product

infixr 9 %
infixr 9 :%

-- | The domain, or source category, of the functor.
type family Dom ftag :: * -> * -> *
-- | The codomain, or target category, of the functor.
type family Cod ftag :: * -> * -> *

-- | Functors map objects and arrows.
class (Category (Dom ftag), Category (Cod ftag)) => Functor ftag where
  -- | @%@ maps arrows.
  (%)  :: ftag -> Dom ftag a b -> Cod ftag (ftag :% a) (ftag :% b)

-- | @:%@ maps objects.
type family ftag :% a :: *


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



data Id ((~>) :: * -> * -> *) = Id

type instance Dom (Id (~>)) = (~>)
type instance Cod (Id (~>)) = (~>)
type instance Id (~>) :% a = a

-- | The identity functor on (~>)
instance Category (~>) => Functor (Id (~>)) where 
  _ % f = f


data (g :.: h) where
  (:.:) :: (Functor g, Functor h, Cod h ~ Dom g) => g -> h -> g :.: h
  
type instance Dom (g :.: h) = Dom h
type instance Cod (g :.: h) = Cod g
type instance (g :.: h) :% a = g :% (h :% a)

-- | The composition of two functors.
instance (Category (Cod g), Category (Dom h)) => Functor (g :.: h) where 
  (g :.: h) % f = g % (h % f)


data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x where
  Const :: Category c2 => Obj c2 x -> Const c1 c2 x
  
type instance Dom (Const c1 c2 x) = c1
type instance Cod (Const c1 c2 x) = c2
type instance Const c1 c2 x :% a = x

-- | The constant functor.
instance (Category c1, Category c2) => Functor (Const c1 c2 x) where 
  Const x % _ = x

-- | The constant functor with the same domain and codomain as f.
type ConstF f = Const (Dom f) (Cod f)


data Opposite f where
  Opposite :: Functor f => f -> Opposite f
  
type instance Dom (Opposite f) = Op (Dom f)
type instance Cod (Opposite f) = Op (Cod f)
type instance Opposite f :% a = f :% a

-- | The dual of a functor
instance (Category (Dom f), Category (Cod f)) => Functor (Opposite f) where
  Opposite f % Op a = Op $ f % a


data OpOp ((~>) :: * -> * -> *) = OpOp

type instance Dom (OpOp (~>)) = Op (Op (~>))
type instance Cod (OpOp (~>)) = (~>)
type instance OpOp (~>) :% a = a

-- | The @Op (Op x) = x@ functor.
instance Category (~>) => Functor (OpOp (~>)) where
  OpOp % Op (Op f) = f


data OpOpInv ((~>) :: * -> * -> *) = OpOpInv

type instance Dom (OpOpInv (~>)) = (~>)
type instance Cod (OpOpInv (~>)) = Op (Op (~>))
type instance OpOpInv (~>) :% a = a

-- | The @x = Op (Op x)@ functor.
instance Category (~>) => Functor (OpOpInv (~>)) where
  OpOpInv % f = Op (Op f)


data EndoHask :: (* -> *) -> * where
  EndoHask :: Prelude.Functor f => EndoHask f
  
type instance Dom (EndoHask f) = (->)
type instance Cod (EndoHask f) = (->)
type instance EndoHask f :% r = f r

-- | 'EndoHask' is a wrapper to turn instances of the 'Functor' class into categorical functors.
instance Functor (EndoHask f) where
  EndoHask % f = fmap f


data Proj1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Proj1

type instance Dom (Proj1 c1 c2) = c1 :**: c2
type instance Cod (Proj1 c1 c2) = c1
type instance Proj1 c1 c2 :% (a1, a2) = a1

-- | 'Proj1' is a bifunctor that projects out the first component of a product.
instance (Category c1, Category c2) => Functor (Proj1 c1 c2) where 
  Proj1 % (f1 :**: _) = f1


data Proj2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) = Proj2

type instance Dom (Proj2 c1 c2) = c1 :**: c2
type instance Cod (Proj2 c1 c2) = c2
type instance Proj2 c1 c2 :% (a1, a2) = a2

-- | 'Proj2' is a bifunctor that projects out the second component of a product.
instance (Category c1, Category c2) => Functor (Proj2 c1 c2) where 
  Proj2 % (_ :**: f2) = f2


data f1 :***: f2 = f1 :***: f2

type instance Dom (f1 :***: f2) = Dom f1 :**: Dom f2
type instance Cod (f1 :***: f2) = Cod f1 :**: Cod f2
type instance (f1 :***: f2) :% (a1, a2) = (f1 :% a1, f2 :% a2)

-- | @f1 :***: f2@ is the product of the functors @f1@ and @f2@.
instance (Functor f1, Functor f2) => Functor (f1 :***: f2) where 
  (g1 :***: g2) % (f1 :**: f2) = (g1 % f1) :**: (g2 % f2)
  
  
data DiagProd ((~>) :: * -> * -> *) = DiagProd

type instance Dom (DiagProd (~>)) = (~>)
type instance Cod (DiagProd (~>)) = (~>) :**: (~>)
type instance DiagProd (~>) :% a = (a, a)

-- | 'DiagProd' is the diagonal functor for products.
instance Category (~>) => Functor (DiagProd (~>)) where 
  DiagProd % f = f :**: f


data Tuple1 (c1 :: * -> * -> *) (c2 :: * -> * -> *) a = Tuple1 (Obj c1 a)

type instance Dom (Tuple1 c1 c2 a1) = c2
type instance Cod (Tuple1 c1 c2 a1) = c1 :**: c2
type instance Tuple1 c1 c2 a1 :% a2 = (a1, a2)

-- | 'Tuple1' tuples with a fixed object on the left.
instance (Category c1, Category c2) => Functor (Tuple1 c1 c2 a1) where
  Tuple1 a % f = a :**: f


data Tuple2 (c1 :: * -> * -> *) (c2 :: * -> * -> *) a = Tuple2 (Obj c2 a)

type instance Dom (Tuple2 c1 c2 a2) = c1
type instance Cod (Tuple2 c1 c2 a2) = c1 :**: c2
type instance Tuple2 c1 c2 a2 :% a1 = (a1, a2)

-- | 'Tuple2' tuples with a fixed object on the right.
instance (Category c1, Category c2) => Functor (Tuple2 c1 c2 a2) where
  Tuple2 a % f = f :**: a


data Hom ((~>) :: * -> * -> *) = Hom  

type instance Dom (Hom (~>)) = Op (~>) :**: (~>)
type instance Cod (Hom (~>)) = (->)
type instance (Hom (~>)) :% (a1, a2) = a1 ~> a2

-- | The Hom functor, Hom(--,--), a bifunctor contravariant in its first argument and covariant in its second argument.
instance Category (~>) => Functor (Hom (~>)) where 
  Hom % (Op f1 :**: f2) = \g -> f2 . g . f1


type x :*-: (~>) = Hom (~>) :.: Tuple1 (Op (~>)) (~>) x
-- | The covariant functor Hom(X,--)
homX_ :: Category (~>) => Obj (~>) x -> x :*-: (~>)
homX_ x = Hom :.: Tuple1 (Op x)

type (~>) :-*: x = Hom (~>) :.: Tuple2 (Op (~>)) (~>) x
-- | The contravariant functor Hom(--,X)
hom_X :: Category (~>) => Obj (~>) x -> (~>) :-*: x
hom_X x = Hom :.: Tuple2 x
