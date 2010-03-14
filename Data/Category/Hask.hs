{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs, EmptyDataDecls #-}
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
  
instance CategoryA (->) a b c where
  (.) = (Prelude..)



newtype instance Funct (->) d (FunctO (->) d f) (FunctO (->) d g) = 
  HaskNat { unHaskNat :: forall a. Component f g a }
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag (->) (~>)) a b where
  Diag % f = HaskNat f


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

initObjInHask :: Limit (Id (->)) Zero
initObjInHask = TerminalUniversal (HaskNat $ magic) (HaskNat unHaskNat)
termObjInHask :: Colimit (Id (->)) ()
termObjInHask = InitialUniversal (HaskNat $ const ()) (HaskNat unHaskNat)

instance PairColimit (->) x y where
  type Coproduct x y = Either x y
  pairColimit = InitialUniversal (Left :***: Right) (HaskNat $ \(l :***: r) -> either l r)
instance PairLimit (->) x y where
  type Product x y = (x, y)
  pairLimit = TerminalUniversal (fst :***: snd) (HaskNat $ \(f :***: s) -> f &&& s)


data ProdInHask = ProdInHask
type instance Dom ProdInHask = Funct Pair (->)
type instance Cod ProdInHask = (->)
type instance F ProdInHask (FunctO Pair (->) f) = (F f Fst, F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA ProdInHask (FunctO Pair (->) f) (FunctO Pair (->) g) where
  ProdInHask % (f :***: g) = f *** g

prodInHaskAdj :: Adjunction (Diag Pair (->)) ProdInHask
prodInHaskAdj = Adjunction { unit = HaskNat $ id &&& id, counit = FunctNat $ fst :***: snd }

data SumInHask = SumInHask
type instance Dom SumInHask = Funct Pair (->)
type instance Cod SumInHask = (->)
type instance F SumInHask (FunctO Pair (->) f) = Either (F f Fst) (F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA SumInHask (FunctO Pair (->) f) (FunctO Pair (->) g) where
  SumInHask % (f :***: g) = f +++ g

sumInHaskAdj :: Adjunction SumInHask (Diag Pair (->))
sumInHaskAdj = Adjunction { unit = FunctNat $ Left :***: Right, counit = HaskNat $ either id id }
