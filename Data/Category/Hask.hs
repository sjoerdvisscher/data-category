{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs, EmptyDataDecls, ScopedTypeVariables #-}
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

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair

type Hask = (->)

instance Apply (->) a b where
  ($$) = ($)

instance CategoryO (->) a where
  id = Prelude.id
  (!) = unHaskNat
  
instance CategoryA (->) a b c where
  (.) = (Prelude..)

newtype instance Nat (->) d f g = 
  HaskNat { unHaskNat :: forall a. Obj a -> Component f g a }
  
  
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag (->) (~>)) a b where
  Diag % f = HaskNat $ const f

-- | Any empty data type is an initial object in Hask.
data Zero
-- With thanks to Conor McBride
magic :: Zero -> a
magic x = x `seq` error "we never get this far"

instance VoidColimit (->) where
  type InitialObject (->) = Zero
  voidColimit = InitialUniversal VoidNat (HaskNat $ \_ VoidNat -> magic)
instance VoidLimit (->) where
  type TerminalObject (->) = ()
  voidLimit = TerminalUniversal VoidNat (HaskNat $ \_ VoidNat -> const ())

-- | An alternative way to define the initial object.
initObjInHask :: Limit (Id (->)) Zero
initObjInHask = TerminalUniversal (HaskNat $ const magic) (HaskNat $ const (! (obj :: Zero)))
-- | An alternative way to define the terminal object.
termObjInHask :: Colimit (Id (->)) ()
termObjInHask = InitialUniversal (HaskNat $ \_ _ -> ()) (HaskNat $ const (! ()))

instance PairColimit (->) x y where
  type Coproduct x y = Either x y
  pairColimit = InitialUniversal (Left :***: Right) (HaskNat $ \_ (l :***: r) -> either l r)
instance PairLimit (->) x y where
  type Product x y = (x, y)
  pairLimit = TerminalUniversal (fst :***: snd) (HaskNat $ \_ (f :***: s) -> f &&& s)

-- | The product functor, Hask^2 -> Hask
data ProdInHask = ProdInHask
type instance Dom ProdInHask = Nat Pair (->)
type instance Cod ProdInHask = (->)
type instance F ProdInHask f = (F f Fst, F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA ProdInHask f g where
  ProdInHask % (f :***: g) = f *** g

-- | The product functor is right adjoint to the diagonal functor.
prodInHaskAdj :: Adjunction (Diag Pair (->)) ProdInHask
prodInHaskAdj = Adjunction { unit = HaskNat $ const (id &&& id), counit = FunctNat $ const (fst :***: snd) }

-- | The coproduct functor, Hask^2 -> Hask
data CoprodInHask = CoprodInHask
type instance Dom CoprodInHask = Nat Pair (->)
type instance Cod CoprodInHask = (->)
type instance F CoprodInHask f = Either (F f Fst) (F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA CoprodInHask f g where
  CoprodInHask % (f :***: g) = f +++ g

-- | The coproduct functor is left adjoint to the diagonal functor.
coprodInHaskAdj :: Adjunction CoprodInHask (Diag Pair (->))
coprodInHaskAdj = Adjunction { unit = FunctNat $ const (Left :***: Right), counit = HaskNat $ const (either id id) }
