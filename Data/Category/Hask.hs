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
import qualified Control.Arrow as A ((***), (&&&), (+++), (|||))

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair
import Data.Category.Product
import Data.Category.Peano
import Data.Category.Dialg

type Hask = (->)

newtype instance Nat (->) d f g = 
  HaskNat { unHaskNat :: forall a. Obj a -> Component f g a }
  
instance Category (->) where
  idNat = HaskNat $ const Prelude.id
  
instance CategoryO (->) a where
  id = Prelude.id
  (!) = unHaskNat
  
instance CategoryA (->) a b c where
  (.) = (Prelude..)

instance Apply (->) a b where
  ($$) = ($)

-- | 'EndoHask' is a wrapper to turn instances of the 'Functor' class into categorical functors.
data EndoHask (f :: * -> *) = EndoHask
type instance Dom (EndoHask f) = (->)
type instance Cod (EndoHask f) = (->)
type instance F (EndoHask f) r = f r
instance Functor f => FunctorA (EndoHask f) a b where
  _ % f = fmap f

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
  pairColimit = InitialUniversal (Left :***: Right) (HaskNat $ \_ (l :***: r) -> l A.||| r)
instance PairLimit (->) x y where
  type Product x y = (x, y)
  pairLimit = TerminalUniversal (fst :***: snd) (HaskNat $ \_ (f :***: s) -> f A.&&& s)

-- | The product functor, Hask^2 -> Hask
data ProdInHask = ProdInHask
type instance Dom ProdInHask = Nat Pair (->)
type instance Cod ProdInHask = (->)
type instance F ProdInHask f = (F f Fst, F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA ProdInHask f g where
  ProdInHask % (f :***: g) = f A.*** g

-- | The product functor is right adjoint to the diagonal functor.
prodInHaskAdj :: Adjunction (Diag Pair (->)) ProdInHask
prodInHaskAdj = Adjunction { unit = HaskNat $ const (id A.&&& id), counit = FunctNat $ const (fst :***: snd) }

-- | The coproduct functor, Hask^2 -> Hask
data CoprodInHask = CoprodInHask
type instance Dom CoprodInHask = Nat Pair (->)
type instance Cod CoprodInHask = (->)
type instance F CoprodInHask f = Either (F f Fst) (F f Snd)
instance (Dom f ~ Pair, Cod f ~ (->), Dom g ~ Pair, Cod g ~ (->)) => FunctorA CoprodInHask f g where
  CoprodInHask % (f :***: g) = f A.+++ g

-- | The coproduct functor is left adjoint to the diagonal functor.
coprodInHaskAdj :: Adjunction CoprodInHask (Diag Pair (->))
coprodInHaskAdj = Adjunction { unit = FunctNat $ const (Left :***: Right), counit = HaskNat $ const (id A.||| id) }

curryAdj :: Adjunction (EndoHask ((,) e)) (EndoHask ((->) e))
curryAdj = Adjunction 
  { unit = HaskNat $ const (\a e -> (e, a))
  , counit = HaskNat $ const (\(x, f) -> f x) }
  
curryAdjInitUniv :: InitialUniversal x (EndoHask ((->) e)) (e, x) -- InitialUniversal x g (F f x)
curryAdjInitUniv = InitialUniversal 
  (unit curryAdj ! (obj :: x))
  (HaskNat $ const (\f -> (\(x, f) -> f x) . fmap f)) -- \h -> (counit curryAdj ! (obj :: x)) . ((obj :: g) % h) 

curryAdjTermUniv :: TerminalUniversal y (EndoHask ((,) e)) (e -> y) -- TerminalUniversal y f (F g y)
curryAdjTermUniv = TerminalUniversal 
  (counit curryAdj ! (obj :: y))
  (HaskNat $ const (\f -> fmap f . (\a e -> (e, a)))) -- \h -> ((obj :: f) % h) . (unit curryAdj ! (obj :: y))
  

-- | FixF provides the initial F-algebra for endofunctors in Hask.
newtype FixF f = InF { outF :: f (FixF f) }

-- | Catamorphisms for endofunctors in Hask.
cataHask :: Functor f => Cata (EndoHask f) a
cataHask (Dialgebra f) = DialgA $ cata f where cata f = f . fmap (cata f) . outF 

-- | Anamorphisms for endofunctors in Hask.
anaHask :: Functor f => Ana (EndoHask f) a
anaHask (Dialgebra f) = DialgA $ ana f where ana f = InF . fmap (ana f) . f 

instance Functor f => VoidColimit (Dialg (EndoHask f) (Id (->))) where
  type InitialObject (Dialg (EndoHask f) (Id (->))) = Algebra (EndoHask f) (FixF f)
  voidColimit = InitialUniversal VoidNat (DialgNat $ \f VoidNat -> cataHask f)
  
instance Functor f => VoidLimit (Dialg (Id (->)) (EndoHask f)) where
  type TerminalObject (Dialg (Id (->)) (EndoHask f)) = Coalgebra (EndoHask f) (FixF f)
  voidLimit = TerminalUniversal VoidNat (DialgNat $ \f VoidNat -> anaHask f)


data NatNum = Z | S NatNum

instance VoidColimit (Peano (->)) where
  type InitialObject (Peano (->)) = PeanoO (->) NatNum
  voidColimit = InitialUniversal VoidNat
    (PeanoNat $ \(PeanoO z s) VoidNat -> let { f Z = z (); f (S n) = s (f n) } in PeanoA f)

instance VoidColimit (Dialg (NatF (->)) (DiagProd (->))) where
  type InitialObject (Dialg (NatF (->)) (DiagProd (->))) = Dialgebra (NatF (->)) (DiagProd (->)) NatNum
  voidColimit = InitialUniversal VoidNat 
    (DialgNat $ \(Dialgebra (z :**: s)) VoidNat -> let { f Z = z (); f (S n) = s (f n) } in DialgA f)

