{-# LANGUAGE TypeFamilies, GADTs, RankNTypes, TypeOperators, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Simplex
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The (augmented) simplex category.
-----------------------------------------------------------------------------
module Data.Category.Simplex (
  
  -- * Simplex Category
    Simplex(..)
  , Z, S
  , suc
  
  -- * Functor
  , Forget(..)
  , Fin(..)
  , Add(..)
  
  -- * The universal monoid
  , universalMonoid
  , Replicate(..)
        
) where
  
import Data.Category
import Data.Category.Product
import Data.Category.Functor
import Data.Category.Monoidal
import Data.Category.Limit


data Z
data S n


-- A Simplex x y structure plots a non-decreasing line, ending with Z
--
--   ^  +-----Z
--   |  |   XXY
--   y  |   Y |
--      |XXXY |
--      XY----+
--         x ->

data Simplex :: * -> * -> * where
  Z ::                    Simplex    Z     Z
  Y :: Simplex x    y  -> Simplex    x  (S y)
  X :: Simplex x (S y) -> Simplex (S x) (S y)

suc :: Obj Simplex n -> Obj Simplex (S n)
suc = X . Y
-- Note: Objects are represented by their identity arrows,
-- which are in the shape of the elements of `iterate suc Z`.

-- | The (augmented) simplex category is the category of finite ordinals and order preserving maps.
instance Category Simplex where
  src Z = Z
  src (Y f) = src f
  src (X f) = suc (src f)
  
  tgt Z = Z
  tgt (Y f) = suc (tgt f)
  tgt (X f) = tgt f
  
  Z   .   f = f
  f   .   Z = f
  Y f .   g = Y (f . g)
  X f . Y g = f . g
  X f . X g = X (X f . g)


-- | The ordinal @0@ is the initial object of the simplex category.
instance HasInitialObject Simplex where
  type InitialObject Simplex = Z
  
  initialObject = Z
  
  initialize Z = Z
  initialize (X (Y f)) = Y (initialize f)

-- | The ordinal @1@ is the terminal object of the simplex category.
instance HasTerminalObject Simplex where
  type TerminalObject Simplex = S Z

  terminalObject = suc Z

  terminate Z = Y Z
  terminate (X (Y f)) = X (terminate f)


data Fin :: * -> * where
  Fz ::          Fin (S n)
  Fs :: Fin n -> Fin (S n)

data Forget = Forget
-- | Turn @Simplex x y@ arrows into @Fin x -> Fin y@ functions.
instance Functor Forget where
  type Dom Forget = Simplex
  type Cod Forget = (->)
  type Forget :% n = Fin n
  Forget % Z   = \x -> x
  Forget % Y f = \x -> Fs ((Forget % f) x)
  Forget % X f = \x -> case x of
    Fz -> Fz
    Fs n -> (Forget % f) n


data Add = Add
-- | Ordinal addition is a bifuntor, it concattenates the maps as it were.
instance Functor Add where
  type Dom Add = Simplex :**: Simplex
  type Cod Add = Simplex
  type Add :% (Z  , n) = n
  type Add :% (S m, n) = S (Add :% (m, n))
  Add % (Z   :**: g) = g
  Add % (Y f :**: g) = Y (Add % (f :**: g))
  Add % (X f :**: g) = X (Add % (f :**: g))

-- | Ordinal addition makes the simplex category a monoidal category, with @0@ as unit.
instance TensorProduct Add where
  type Unit Add = Z
  unitObject Add = Z
  
  leftUnitor     Add       a   = a
  leftUnitorInv  Add       a   = a
  rightUnitor    Add       Z   = Z
  rightUnitor    Add (X (Y n)) = X (Y (rightUnitor Add n))
  rightUnitorInv Add       Z   = Z
  rightUnitorInv Add (X (Y n)) = X (Y (rightUnitorInv Add n))
  associator     Add Z       Z   n = n
  associator     Add Z (X (Y m)) n = X (Y (associator Add Z m n))
  associator     Add (X (Y l)) m n = X (Y (associator Add l m n))
  associatorInv  Add Z       Z   n = n
  associatorInv  Add Z (X (Y m)) n = X (Y (associatorInv Add Z m n))
  associatorInv  Add (X (Y l)) m n = X (Y (associatorInv Add l m n))


-- | The maps @0 -> 1@ and @2 -> 1@ form a monoid, which is universal, c.f. `Replicate`.
universalMonoid :: MonoidObject Add (S Z)
universalMonoid = MonoidObject { unit = Y Z, multiply = X (X (Y Z)) }

data Replicate f a = Replicate f (MonoidObject f a)
-- | Replicate a monoid a number of times.
instance TensorProduct f => Functor (Replicate f a) where
  type Dom (Replicate f a) = Simplex
  type Cod (Replicate f a) = Cod f
  type Replicate f a :% Z = Unit f
  type Replicate f a :% S n = f :% (a, Replicate f a :% n)
  Replicate f _ % Z = unitObject f
  Replicate f m % Y n = f % (unit m :**: tgt n') . leftUnitorInv f (tgt n') . n' where n' = Replicate f m % n
  Replicate f m % X (Y n) = f % (tgt (unit m) :**: (Replicate f m % n))
  Replicate f m % X (X n) = n' . (f % (multiply m :**: b)) . associatorInv f a a b
    where
      n' = Replicate f m % X n
      a = tgt (unit m)
      b = src (Replicate f m % n)
