{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Functor
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Functor where
  
import Data.Category


-- | Functor category Funct(C, D), or D^C.
-- Objects of Funct(C, D) are functors from C to D.
-- Arrows of Funct(C, D) are natural transformations.
-- Each category C needs its own data instance.
data family Funct (c :: * -> * -> *) (d :: * -> * -> *) (f :: *) (g :: *) :: *

-- | @f :~> g@ is a natural transformation from functor f to functor g.
type f :~> g = (c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) => Funct c d f g

-- | Natural transformations are built up of components, 
-- one for each object @z@ in the domain category of @f@ and @g@.
-- This type synonym can be used when creating data instances of @Funct@.
type Component f g z = Cod f (F f z) (F g z)

-- | 'GetComponent' is a typeclass to retrieve a component from a natural transformation for a specific object.
class GetComponent c d z where
  (!) :: Funct c d f g -> Obj z -> Component f g z


-- | Arrows of the category Funct(Funct(C, D), E)
-- I.e. natural transformations between functors of type D^C -> E
data instance Funct (Funct c d) e f g = 
  FunctNat { unFunctNat :: forall h. (Dom h ~ c, Cod h ~ d) => Obj h -> Component f g h }

instance (Dom z ~ c, Cod z ~ d) => GetComponent (Funct c d) e z where
    (!) = unFunctNat



-- | The diagonal functor from (index-) category J to (~>).
data Diag (j :: * -> * -> *) ((~>) :: * -> * -> *) = Diag
type instance Dom (Diag j (~>)) = (~>)
type instance Cod (Diag j (~>)) = Funct j (~>)
type instance F (Diag j (~>)) a = Const j (~>) a


type InitMorF x u = (x :*-: Cod u) :.: u
type TermMorF x u = (Cod u :-*: x) :.: u
data InitialUniversal  x u a = InitialUniversal  (F (InitMorF x u) a) (InitMorF x u :~> (a :*-: Dom u))
data TerminalUniversal x u a = TerminalUniversal (F (TermMorF x u) a) (TermMorF x u :~> (Dom u :-*: a))

-- |A cone from N to F is a natural transformation from the constant functor to N to F.
type Cone   f n = Const (Dom f) (Cod f) n :~> f
-- |A co-cone from F to N is a natural transformation from F to the constant functor to N.
type Cocone f n = f :~> Const (Dom f) (Cod f) n

type Limit   f l = TerminalUniversal f (Diag (Dom f) (Cod f)) l
type Colimit f l = InitialUniversal  f (Diag (Dom f) (Cod f)) l

data Adjunction f g = Adjunction 
  { unit :: Id (Dom f) :~> (g :.: f)
  , counit :: (f :.: g) :~> Id (Dom g)
  }