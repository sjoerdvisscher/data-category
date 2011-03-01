{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, FlexibleInstances, UndecidableInstances, GADTs, RankNTypes #-}
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
  , (:*-:)(..)
  , (:-*:)(..)
  , Opposite(..)
  , EndoHask(..)
  
  -- * Universal properties
  , Representation(..)
  , unrepresent
  , covariantHomRepr
  , contravariantHomRepr
  , InitialUniversal
  , initialUniversal
  , TerminalUniversal
  , terminalUniversal
  
) where
  
import Prelude hiding ((.), Functor)
import qualified Prelude
  
import Data.Category

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



-- | The identity functor on (~>)
data Id ((~>) :: * -> * -> *) = Id

type instance Dom (Id (~>)) = (~>)
type instance Cod (Id (~>)) = (~>)
type instance Id (~>) :% a = a

instance Category (~>) => Functor (Id (~>)) where 
  _ % f = f


-- | The composition of two functors.
data (g :.: h) where
  (:.:) :: (Functor g, Functor h, Cod h ~ Dom g) => g -> h -> g :.: h
  
type instance Dom (g :.: h) = Dom h
type instance Cod (g :.: h) = Cod g
type instance (g :.: h) :% a = g :% (h :% a)

instance (Category (Cod g), Category (Dom h)) => Functor (g :.: h) where 
  (g :.: h) % f = g % (h % f)


-- | The constant functor.
data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x where
  Const :: Category c2 => Obj c2 x -> Const c1 c2 x
  
type instance Dom (Const c1 c2 x) = c1
type instance Cod (Const c1 c2 x) = c2
type instance Const c1 c2 x :% a = x

instance (Category c1, Category c2) => Functor (Const c1 c2 x) where 
  Const x % _ = x

type ConstF f = Const (Dom f) (Cod f)

  
-- | The covariant functor Hom(X,--)
data (:*-:) :: * -> (* -> * -> *) -> * where
  HomX_ :: Category (~>) => Obj (~>) x -> x :*-: (~>)
  
type instance Dom (x :*-: (~>)) = (~>)
type instance Cod (x :*-: (~>)) = (->)
type instance (x :*-: (~>)) :% a = x ~> a

instance Category (~>) => Functor (x :*-: (~>)) where 
  HomX_ _ % f = (f .)


-- | The contravariant functor Hom(--,X)
data (:-*:) :: (* -> * -> *) -> * -> * where
  Hom_X :: Category (~>) => Obj (~>) x -> (~>) :-*: x

type instance Dom ((~>) :-*: x) = Op (~>)
type instance Cod ((~>) :-*: x) = (->)
type instance ((~>) :-*: x) :% a = a ~> x

instance Category (~>) => Functor ((~>) :-*: x) where 
  Hom_X _ % Op f = (. f)


-- | The dual of a functor
data Opposite f where
  Opposite :: Functor f => f -> Opposite f
  
type instance Dom (Opposite f) = Op (Dom f)
type instance Cod (Opposite f) = Op (Cod f)
type instance Opposite f :% a = f :% a

instance (Category (Dom f), Category (Cod f)) => Functor (Opposite f) where
  Opposite f % Op a = Op $ f % a


-- | 'EndoHask' is a wrapper to turn instances of the 'Functor' class into categorical functors.
data EndoHask :: (* -> *) -> * where
  EndoHask :: Prelude.Functor f => EndoHask f
  
type instance Dom (EndoHask f) = (->)
type instance Cod (EndoHask f) = (->)
type instance EndoHask f :% r = f r

instance Functor (EndoHask f) where
  EndoHask % f = fmap f


data Representation f repObj = Representation
  { representedFunctor :: f
  , representingObject :: Obj (Dom f) repObj
  , represent          :: (Dom f ~ (~>), Cod f ~ (->)) => Obj (~>) z -> f :% z -> repObj ~> z
  , universalElement   :: (Dom f ~ (~>), Cod f ~ (->)) => f :% repObj
  }

unrepresent :: (Functor f, Dom f ~ (~>), Cod f ~ (->)) => Representation f repObj -> repObj ~> z -> f :% z
unrepresent rep h = representedFunctor rep % h $ universalElement rep

covariantHomRepr :: Category (~>) => Obj (~>) x -> Representation (x :*-: (~>)) x
covariantHomRepr x = Representation
  { representedFunctor = HomX_ x
  , representingObject = x
  , represent          = \_ -> id
  , universalElement   = x
  }

contravariantHomRepr :: Category (~>) => Obj (~>) x -> Representation ((~>) :-*: x) x
contravariantHomRepr x = Representation
  { representedFunctor = Hom_X x
  , representingObject = Op x
  , represent          = \_ h -> Op h
  , universalElement   = x
  }

-- | An initial universal property, a universal morphism from x to u.
type InitialUniversal x u a = Representation ((x :*-: Cod u) :.: u) a
initialUniversal :: Functor u
                 => u 
                 -> Obj (Dom u) a 
                 -> Cod u x (u :% a) 
                 -> (forall y. Obj (Dom u) y -> Cod u x (u :% y) -> Dom u a y) 
                 -> InitialUniversal x u a
initialUniversal u obj mor factorizer = Representation
  { representedFunctor = HomX_ (src mor) :.: u
  , representingObject = obj
  , represent          = factorizer
  , universalElement   = mor
  }
  
-- | A terminal universal property, a universal morphism from u to x.
type TerminalUniversal x u a = Representation ((Cod u :-*: x) :.: Opposite u) a
terminalUniversal :: Functor u
                  => u 
                  -> Obj (Dom u) a
                  -> Cod u (u :% a) x
                  -> (forall y. Obj (Dom u) y -> Cod u (u :% y) x -> Dom u y a) 
                  -> TerminalUniversal x u a
terminalUniversal u obj mor factorizer = Representation
  { representedFunctor = Hom_X (tgt mor) :.: Opposite u
  , representingObject = Op obj
  , represent          = \(Op y) f -> Op (factorizer y f)
  , universalElement   = mor
  }
