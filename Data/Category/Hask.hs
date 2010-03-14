{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs, EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Hask
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Hask where

import Prelude hiding ((.), id)
import qualified Prelude
import Control.Arrow ((&&&), (***), (+++))
-- Getting desperate
import Unsafe.Coerce

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair

type Hask = (->)

instance Apply (->) a b where
  ($$) = ($)

instance CategoryO (->) a where
  id = Prelude.id
  
instance CategoryA (->) a b c where
  (.) = (Prelude..)



newtype instance Funct (->) d (FunctO (->) d f) (FunctO (->) d g) = 
  HaskNat (forall a. Component f g a)

-- | This isn't really working, and there really needs to be a solution for this.
unHaskNat :: Funct (->) d (FunctO (->) d f) (FunctO (->) d g) -> Component f g a
unHaskNat (HaskNat c) = unsafeCoerce c

instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag (->) (~>)) a b where
  Diag % f = HaskNat f

-- | Any empty data type is an initial object in Hask.
data Zero
-- With thanks to Conor McBride
magic :: Zero -> a
magic x = x `seq` error "we never get this far"

instance VoidColimit (->) where
  type InitialObject (->) = Zero
  voidColimit = InitialUniversal VoidNat (HaskNat $ \VoidNat -> magic)
instance VoidLimit (->) where
  type TerminalObject (->) = ()
  voidLimit = TerminalUniversal VoidNat (HaskNat $ \VoidNat -> const ())

-- | An alternative way to define the initial object.
initObjInHask :: Limit (Id (->)) Zero
initObjInHask = TerminalUniversal (HaskNat $ magic) (HaskNat unHaskNat)
-- | An alternative way to define the terminal object.
termObjInHask :: Colimit (Id (->)) ()
termObjInHask = InitialUniversal (HaskNat $ const ()) (HaskNat unHaskNat)

instance PairColimit (->) x y where
  type Coproduct x y = Either x y
  pairColimit = InitialUniversal (Left :***: Right) (HaskNat $ \(l :***: r) -> either l r)
instance PairLimit (->) x y where
  type Product x y = (x, y)
  pairLimit = TerminalUniversal (fst :***: snd) (HaskNat $ \(f :***: s) -> f &&& s)

-- | The product functor, Hask^2 -> Hask
data ProdInHask = ProdInHask
type instance Dom ProdInHask = Funct Pair (->)
type instance Cod ProdInHask = (->)
type instance F ProdInHask (FunctO Pair (->) f) = (F f Fst, F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA ProdInHask (FunctO Pair (->) f) (FunctO Pair (->) g) where
  ProdInHask % (f :***: g) = f *** g

-- | The product functor is right adjoint to the diagonal functor.
prodInHaskAdj :: Adjunction (Diag Pair (->)) ProdInHask
prodInHaskAdj = Adjunction { unit = HaskNat $ id &&& id, counit = FunctNat $ fst :***: snd }

-- | The coproduct functor, Hask^2 -> Hask
data CoprodInHask = CoprodInHask
type instance Dom CoprodInHask = Funct Pair (->)
type instance Cod CoprodInHask = (->)
type instance F CoprodInHask (FunctO Pair (->) f) = Either (F f Fst) (F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA CoprodInHask (FunctO Pair (->) f) (FunctO Pair (->) g) where
  CoprodInHask % (f :***: g) = f +++ g

-- | The coproduct functor is left adjoint to the diagonal functor.
coprodInHaskAdj :: Adjunction CoprodInHask (Diag Pair (->))
coprodInHaskAdj = Adjunction { unit = FunctNat $ Left :***: Right, counit = HaskNat $ either id id }
