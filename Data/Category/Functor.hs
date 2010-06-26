{-# LANGUAGE TypeOperators, TypeFamilies, EmptyDataDecls, FlexibleContexts, UndecidableInstances, GADTs, RankNTypes #-}
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
  , Obj(..)
  , CatW

  -- * Functors
  , F
  , Dom
  , Cod
  , Functor(..)
  
  -- ** Functor instances
  , Id(..)
  , (:.:)(..)
  , Const(..), ConstF
  , (:*-:)(..)
  , (:-*:)(..)
  , EndoHask(..)
  
  -- * Universal properties
  , InitialUniversal(..)
  , TerminalUniversal(..)

) where
  
import Prelude hiding (id, (.), Functor)
import qualified Prelude
  
import Data.Category


-- | Functors are represented by a type tag. The type family 'F' turns the tag into the actual functor.
type family F ftag a :: *
-- | The domain, or source category, of the functor.
type family Dom ftag :: * -> * -> *
-- | The codomain, or target category, of the funcor.
type family Cod ftag :: * -> * -> *

-- | The mapping of arrows by covariant functors.
-- To make this type check, we need to pass the type tag along.
class Functor ftag where
  (%%) :: ftag -> Obj (Dom ftag) a -> Obj (Cod ftag) (F ftag a)
  (%)  :: ftag -> Dom ftag a b -> Cod ftag (F ftag a) (F ftag b)


-- | Functors are arrows in the category Cat.
data Cat :: * -> * -> * where
  CatA :: (Functor ftag, Category (Dom ftag), Category (Cod ftag)) => ftag -> Cat (CatW (Dom ftag)) (CatW (Cod ftag))

-- | We need a wrapper here because objects need to be of kind *, and categories are of kind * -> * -> *.
data CatW :: (* -> * -> *) -> *


instance Category Cat where
  
  -- | The objects in the category Cat are the categories themselves.
  data Obj Cat a where
    CatO :: Category (~>) => Obj Cat (CatW (~>))
    
  src (CatA _) = CatO
  tgt (CatA _) = CatO
  
  id CatO           = CatA Id
  CatA f1 . CatA f2 = CatA (f1 :.: f2)



-- | The identity functor on (~>)
data Id ((~>) :: * -> * -> *) = Id

type instance Dom (Id (~>)) = (~>)
type instance Cod (Id (~>)) = (~>)
type instance F (Id (~>)) a = a

instance Functor (Id (~>)) where 
  _ %% x = x
  _ %  f = f


-- | The composition of two functors.
data (g :.: h) where
  (:.:) :: (Functor g, Functor h, Cod h ~ Dom g) => g -> h -> g :.: h
  
type instance Dom (g :.: h) = Dom h
type instance Cod (g :.: h) = Cod g
type instance F (g :.: h) a = F g (F h a)

instance Functor (g :.: h) where 
  (g :.: h) %% x = g %% (h %% x)
  (g :.: h) %  f = g %  (h %  f)


-- | The constant functor.
data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x where
  Const :: Category c2 => Obj c2 x -> Const c1 c2 x
  
type instance Dom (Const c1 c2 x) = c1
type instance Cod (Const c1 c2 x) = c2
type instance F (Const c1 c2 x) a = x

instance Functor (Const c1 c2 x) where 
  Const x %% _ = x
  Const x %  _ = id x

type ConstF f = Const (Dom f) (Cod f)

  
-- | The covariant functor Hom(X,--)
data (:*-:) :: * -> (* -> * -> *) -> * where
  HomX_ :: Category (~>) => Obj (~>) x -> x :*-: (~>)
  
type instance Dom (x :*-: (~>)) = (~>)
type instance Cod (x :*-: (~>)) = (->)
type instance F (x :*-: (~>)) a = x ~> a

instance Functor (x :*-: (~>)) where 
  HomX_ _ %% _ = HaskO
  HomX_ _ %  f = (f .)


-- | The contravariant functor Hom(--,X)
data (:-*:) :: (* -> * -> *) -> * -> * where
  Hom_X :: Category (~>) => Obj (~>) x -> (~>) :-*: x

type instance Dom ((~>) :-*: x) = Op (~>)
type instance Cod ((~>) :-*: x) = (->)
type instance F ((~>) :-*: x) a = a ~> x

instance Functor ((~>) :-*: x) where 
  Hom_X _ %% _   = HaskO
  Hom_X _ % Op f = (. f)


-- | The dual of a functor
data DualFunctor f where
  DualFunctor :: Functor f => f -> DualFunctor f
  
type instance Dom (DualFunctor f) = Op (Dom f)
type instance Cod (DualFunctor f) = Op (Cod f)
type instance F (DualFunctor f) a = F f a

instance Functor (DualFunctor f) where
  DualFunctor f %% OpObj x = OpObj $ f %% x
  DualFunctor f % Op a = Op $ f % a


-- | 'EndoHask' is a wrapper to turn instances of the 'Functor' class into categorical functors.
data EndoHask :: (* -> *) -> * where
  EndoHask :: Prelude.Functor f => EndoHask f
  
type instance Dom (EndoHask f) = (->)
type instance Cod (EndoHask f) = (->)
type instance F (EndoHask f) r = f r

instance Functor (EndoHask f) where
  EndoHask %% HaskO = HaskO
  EndoHask % f = fmap f


data InitialUniversal  x u a = InitialUniversal
  { iuObject :: Obj (Dom u) a
  , initialMorphism :: Cod u x (F u a)
  , initialFactorizer :: forall y. Obj (Dom u) y -> Cod u x (F u y) -> Dom u a y }
  
data TerminalUniversal x u a = TerminalUniversal 
  { tuObject :: Obj (Dom u) a
  , terminalMorphism :: Cod u (F u a) x
  , terminalFactorizer :: forall y. Obj (Dom u) y -> Cod u (F u y) x -> Dom u y a }
