{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, ScopedTypeVariables, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs #-}
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
module Data.Category.NaturalTransformation where
  
import Prelude hiding ((.), id, Functor)

import Data.Category
import Data.Category.Functor


-- | @f :~> g@ is a natural transformation from functor f to functor g.
type f :~> g = (c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) => Nat c d f g

data Nat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  Nat :: (Functor f, Functor g, c ~ Dom f, c ~ Dom g, d ~ Cod f, d ~ Cod g) 
    => f -> g -> (forall a. Obj c a -> Component f g a) -> Nat c d f g

-- | Natural transformations are built up of components, 
-- one for each object @z@ in the domain category of @f@ and @g@.
type Component f g z = Cod f (F f z) (F g z)


-- | Functor category D^C.
-- Objects of D^C are functors from C to D.
-- Arrows of D^C are natural transformations.
instance (Category c, Category d) => Category (Nat c d) where
  
  data Obj (Nat c d) a where
    NatO :: Functor f => f -> Obj (Nat (Dom f) (Cod f)) f
    
  src (Nat f _ _) = NatO f
  tgt (Nat _ g _) = NatO g
  
  id (NatO f)               = Nat f f $ \i -> id $ f %% i
  Nat _ h ngh . Nat f _ nfg = Nat f h $ \i -> ngh i . nfg i


-- This data type can be used when creating data instances of @Nat@.
data Comp :: * -> * -> * -> * where
  Com :: Cod f (F f z) (F g z) -> Comp f g z

unCom :: Comp f g z -> Cod f (F f z) (F g z)
unCom (Com c) = c

-- | 'n ! a' returns the component for the object @a@ of a natural transformation @n@.
(!) :: (Cod f ~ d, Cod g ~ d) => Nat (~>) d f g -> Obj (~>) a -> d (F f a) (F g a)
Nat _ _ n ! x = n x

precompose :: (Functor k, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Dom k ~ b, Cod k ~ c) 
  => k -> Nat c d f g -> Nat b d (f :.: k) (g :.: k)
precompose  k (Nat f g n) = Nat (f :.: k) (g :.: k) $ n . (k %%)

postcompose :: (Functor h, Dom f ~ c, Dom g ~ c, Cod f ~ d, Cod g ~ d, Dom h ~ d, Cod h ~ e) 
  => h -> Nat c d f g -> Nat c e (h :.: f) (h :.: g)
postcompose h (Nat f g n) = Nat (h :.: f) (h :.: g) $ (h %) . n



-- | The diagonal functor from (index-) category J to (~>).
data Diag :: (* -> * -> *) -> (* -> * -> *) -> * where
  Diag :: (Category j, Category (~>)) => Diag j (~>)
type instance Dom (Diag j (~>)) = (~>)
type instance Cod (Diag j (~>)) = Nat j (~>)
type instance F (Diag j (~>)) a = Const j (~>) a
instance Functor (Diag j (~>)) where 
  Diag %% x = NatO $ Const x
  Diag %  f = Nat (Const $ src f) (Const $ tgt f) $ const f

type DiagF f = Diag (Dom f) (Cod f)
type ConstF f = Const (Dom f) (Cod f)



-- | A cone from N to F is a natural transformation from the constant functor to N to F.
type Cone   f n = ConstF f n :~> f
-- | A co-cone from F to N is a natural transformation from F to the constant functor to N.
type Cocone f n = f :~> ConstF f n

type Limit   f l = TerminalUniversal f (DiagF f) l
type Colimit f l = InitialUniversal  f (DiagF f) l

unNatOConst :: Obj (Nat j (~>)) (Const j (~>) l) -> Obj (~>) l
unNatOConst (NatO (Const x)) = x

limitObject :: (Category (~>), Category (Dom f), Cod f ~ (~>)) => Limit f l -> Obj (~>) l
limitObject = unNatOConst . src . terminalMorphism

colimitObject :: (Category (~>), Category (Dom f), Cod f ~ (~>)) => Colimit f l -> Obj (~>) l
colimitObject = unNatOConst . tgt . initialMorphism


class Representable f x where
  represent :: (x :*-: Dom f) :~> f
  unrepresent :: f :~> (x :*-: Dom f)