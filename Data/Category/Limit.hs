{-# LANGUAGE 
  EmptyDataDecls, 
  FlexibleContexts, 
  FlexibleInstances, 
  GADTs, 
  MultiParamTypeClasses,
  RankNTypes, 
  ScopedTypeVariables,
  TypeOperators, 
  TypeFamilies,
  UndecidableInstances  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Limit
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Limit where

import Prelude hiding ((.), id, Functor, product)
import qualified Control.Arrow as A ((&&&), (***), (|||), (+++))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Void
import Data.Category.Pair
import Data.Category.Unit
import Data.Category.Product
import Data.Category.Discrete


-- | The diagonal functor from (index-) category J to (~>).
data Diag :: (* -> * -> *) -> (* -> * -> *) -> * where
  Diag :: (Category j, Category (~>)) => Diag j (~>)
  
type instance Dom (Diag j (~>)) = (~>)
type instance Cod (Diag j (~>)) = Nat j (~>)
type instance Diag j (~>) :% a = Const j (~>) a

instance Functor (Diag j (~>)) where 
  Diag %% x = NatO $ Const x
  Diag %  f = Nat (Const $ src f) (Const $ tgt f) $ const f

type DiagF f = Diag (Dom f) (Cod f)



-- | A cone from N to F is a natural transformation from the constant functor to N to F.
type Cone   f n = Nat (Dom f) (Cod f) (ConstF f n) f

-- | A co-cone from F to N is a natural transformation from F to the constant functor to N.
type Cocone f n = Nat (Dom f) (Cod f) f (ConstF f n)


-- | The vertex (or apex) of a cone.
coneVertex :: Cone f n -> Obj (Cod f) n
coneVertex (Nat (Const x) _ _) = x

-- | The vertex (or apex) of a co-cone.
coconeVertex :: Cocone f n -> Obj (Cod f) n
coconeVertex (Nat _ (Const x) _) = x


-- | Limits in a category @(~>)@ by means of a diagram of type @j@, which is a functor from @j@ to @(~>)@.
class (Category j, Functor f {- Dom f ~ j -}) => HasLimit j f where
  
  type Limit j f :: *
  
  limit :: (Dom f ~ j, Cod f ~ (~>)) => f -> Cone f (Limit j f)
  limit f = terminalMorphism (limitUniversal f)
  
  limitFactorizer :: (Dom f ~ j, Cod f ~ (~>)) => f -> Cone f n -> Cod f n (Limit j f)
  limitFactorizer f c = terminalFactorizer (limitUniversal f) (coneVertex c) c

  limitUniversal :: (Dom f ~ j, Cod f ~ (~>)) => f -> TerminalUniversal f (Diag j (~>)) (Limit j f)
  limitUniversal f = let l = limit f in TerminalUniversal
    { tuObject           = coneVertex l
    , terminalMorphism   = l
    , terminalFactorizer = \_ s -> limitFactorizer f s
    }


-- | Colimits in a category @(~>)@ by means of a diagram of type @j@, which is a functor from @j@ to @(~>)@.
class (Category j, Functor f {- Dom f ~ j -}) => HasColimit j f where
  
  type Colimit j f :: *
  
  colimit :: (Dom f ~ j, Cod f ~ (~>)) => f -> Cocone f (Colimit j f)
  colimit f = initialMorphism (colimitUniversal f)
    
  colimitFactorizer :: (Dom f ~ j, Cod f ~ (~>)) => f -> Cocone f n -> Cod f (Colimit j f) n
  colimitFactorizer f c = initialFactorizer (colimitUniversal f) (coconeVertex c) c

  colimitUniversal :: (Dom f ~ j, Cod f ~ (~>)) => f -> InitialUniversal f (DiagF f) (Colimit j f)
  colimitUniversal f = let l = colimit f in InitialUniversal
    { iuObject          = coconeVertex l
    , initialMorphism   = l
    , initialFactorizer = \_ s -> colimitFactorizer f s
    }



data LimitFunctor :: (* -> * -> *) -> (* -> * -> *) -> * where
  LimitFunctor :: (Category (~>), Category j)
    => (forall f. (Dom f ~ j, Cod f ~ (~>)) => f -> TerminalUniversal f (Diag j (~>)) (Limit j f)) 
    -> LimitFunctor j (~>)

type instance Dom (LimitFunctor j (~>)) = Nat j (~>)
type instance Cod (LimitFunctor j (~>)) = (~>)
type instance LimitFunctor j (~>) :% f = Limit j f

instance Functor (LimitFunctor j (~>)) where
  LimitFunctor univ %% NatO f       = tuObject (univ f)
  LimitFunctor univ % n@(Nat f g _) = terminalFactorizer (univ g) (tuObject (univ f)) (n . terminalMorphism (univ f))


liftLimit :: (Dom f ~ j, Dom g ~ j, Cod f ~ (~>), Cod g ~ (~>), HasLimit j f, HasLimit j g, Category (~>)) 
  => Nat j (~>) f g -> Limit j f ~> Limit j g
liftLimit n@(Nat f g _) = limitFactorizer g (n . limit f)

    
data ColimitFunctor :: (* -> * -> *) -> (* -> * -> *) -> * where
  ColimitFunctor :: (Category (~>), Category j) 
    => (forall f. (Dom f ~ j, Cod f ~ (~>)) => f -> InitialUniversal f (DiagF f) (Colimit j f))
    -> ColimitFunctor j (~>)
  
type instance Dom (ColimitFunctor j (~>)) = Nat j (~>)
type instance Cod (ColimitFunctor j (~>)) = (~>)
type instance ColimitFunctor j (~>) :% f = Colimit j f

instance Functor (ColimitFunctor j (~>)) where
  ColimitFunctor univ %% NatO f       = iuObject (univ f)
  ColimitFunctor univ % n@(Nat f g _) = initialFactorizer (univ f) (iuObject (univ g)) (initialMorphism (univ g) . n)


liftColimit :: (Dom f ~ j, Dom g ~ j, Cod f ~ (~>), Cod g ~ (~>), HasColimit j f, HasColimit j g, Category (~>)) 
  => Nat j (~>) f g -> Colimit j f ~> Colimit j g
liftColimit n@(Nat f g _) = colimitFactorizer f (colimit g . n)



-- | A terminal object is the limit of the functor from /0/ to (~>).
class Category (~>) => HasTerminalObject (~>) where
  
  type TerminalObject (~>) :: *
  
  terminalObject :: Obj (~>) (TerminalObject (~>))
  
  terminate :: Obj (~>) a -> a ~> TerminalObject (~>)


instance (Functor f, Dom f ~ Void, HasTerminalObject (Cod f)) => HasLimit Void f where
  
  type Limit Void f = TerminalObject (Cod f)

  limit f = voidNat (Const terminalObject) f
  
  limitFactorizer _ = terminate . coneVertex


-- | @()@ is the terminal object in @Hask@.
instance HasTerminalObject (->) where
  
  type TerminalObject (->) = ()
  
  terminalObject = HaskO
  
  terminate HaskO _ = ()

-- | @Unit@ is the terminal category.
instance HasTerminalObject Cat where
  
  type TerminalObject Cat = CatW Unit
  
  terminalObject = CatO
  
  terminate CatO = CatA $ Const UnitO


-- | An initial object is the colimit of the functor from /0/ to (~>).
class Category (~>) => HasInitialObject (~>) where
  
  type InitialObject (~>) :: *
  
  initialObject :: Obj (~>) (InitialObject (~>))

  initialize :: Obj (~>) a -> InitialObject (~>) ~> a


instance (Functor f, Dom f ~ Void, HasInitialObject (Cod f)) => HasColimit Void f where
  
  type Colimit Void f = InitialObject (Cod f)

  colimit f = voidNat f (Const initialObject)
  
  colimitFactorizer _ = initialize . coconeVertex


-- | Any empty data type is an initial object in Hask.
data Zero

instance HasInitialObject (->) where
  
  type InitialObject (->) = Zero
  
  initialObject = HaskO
  
  -- With thanks to Conor McBride
  initialize HaskO x = x `seq` error "we never get this far"

instance HasInitialObject Cat where
  
  type InitialObject Cat = CatW Void
  
  initialObject = CatO
  
  initialize CatO = CatA VoidDiagram



type family Product ((~>) :: * -> * -> *) x y :: *

-- | The product of 2 objects is the limit of the functor from Pair to (~>).
class Category (~>) => HasProducts (~>) where
  
  product :: Obj (~>) x -> Obj (~>) y -> Obj (~>) (Product (~>) x y)
  
  proj :: Obj (~>) x -> Obj (~>) y -> (Product (~>) x y ~> x, Product (~>) x y ~> y)

  (&&&) :: (a ~> x) -> (a ~> y) -> (a ~> Product (~>) x y)

  (***) :: (a1 ~> b1) -> (a2 ~> b2) -> (Product (~>) a1 a2 ~> Product (~>) b1 b2)
  l *** r = (l . proj1) &&& (r . proj2) where
    (proj1, proj2) = proj (src l) (src r)


instance (Functor f, Dom f ~ Pair, HasProducts (Cod f)) => HasLimit Pair f where
  
  type Limit Pair f = Product (Cod f) (f :% P1) (f :% P2)

  limit f = pairNat (Const prod) f (Com . fst $ prj) (Com . snd $ prj)
    where
      x = f %% Fst
      y = f %% Snd
      prod = product x y
      prj = proj x y
  
  limitFactorizer _ c = (c ! Fst) &&& (c ! Snd)


type instance Product (->) x y = (x, y)

instance HasProducts (->) where
  
  product HaskO HaskO = HaskO
  
  proj _ _ = (fst, snd)
  
  (&&&) = (A.&&&)
  (***) = (A.***)

type instance Product Cat (CatW c1) (CatW c2) = CatW (c1 :*: c2)

instance HasProducts Cat where
  
  product CatO CatO = CatO
  
  proj CatO CatO = (CatA Proj1, CatA Proj2)
  
  CatA f1 &&& CatA f2 = CatA ((f1 :***: f2) :.: DiagProd)
  CatA f1 *** CatA f2 = CatA (f1 :***: f2)



type family Coproduct ((~>) :: * -> * -> *) x y :: *

-- | The coproduct of 2 objects is the colimit of the functor from Pair to (~>).
class Category (~>) => HasCoproducts (~>) where

  coproduct :: Obj (~>) x -> Obj (~>) y -> Obj (~>) (Coproduct (~>) x y)
  
  inj :: Obj (~>) x -> Obj (~>) y -> (x ~> Coproduct (~>) x y, y ~> Coproduct (~>) x y)

  (|||) :: (x ~> a) -> (y ~> a) -> (Coproduct (~>) x y ~> a)
    
  (+++) :: (a1 ~> b1) -> (a2 ~> b2) -> (Coproduct (~>) a1 a2 ~> Coproduct (~>) b1 b2)
  l +++ r = (inj1 . l) ||| (inj2 . r) where
    (inj1, inj2) = inj (tgt l) (tgt r)
    

instance (Functor f, Dom f ~ Pair, HasCoproducts (Cod f)) => HasColimit Pair f where
  
  type Colimit Pair f = Coproduct (Cod f) (f :% P1) (f :% P2)

  colimit f = pairNat f (Const cop) (Com . fst $ i) (Com . snd $ i)
    where
      x = f %% Fst
      y = f %% Snd
      cop = coproduct x y
      i = inj x y
  
  colimitFactorizer _ c = (c ! Fst) ||| (c ! Snd)


type instance Coproduct (->) x y = Either x y

instance HasCoproducts (->) where
  
  coproduct HaskO HaskO = HaskO
  
  inj _ _ = (Left, Right)
  
  (|||) = (A.|||)
  (+++) = (A.+++)


instance (Functor f, Dom f ~ Discrete Z, HasTerminalObject (Cod f)) => HasLimit (Discrete Z) f where

  type Limit (Discrete Z) f = TerminalObject (Cod f)
  
  limit f = Nat (Const terminalObject) f magicZO
  
  limitFactorizer _ = terminate . coneVertex
  
instance (Functor f, Dom f ~ Discrete (S n), HasProducts (Cod f), Category (Discrete n), HasLimit (Discrete n) (Next n f)) 
  => HasLimit (Discrete (S n)) f where
    
  type Limit (Discrete (S n)) f = Product (Cod f) (f :% Z) (Limit (Discrete n) (Next n f))

  limit f = undefined -- diagNat (Const prod) f (Com . fst $ prj) (Com . snd $ prj)
    where
      x = (f %% OZ)
      cone = limit (Next f)
      y = coneVertex cone
      prod = product x y
      prj = proj x y
      
  -- LimitFunctor % Nat f g n = n OZ      ***       (LimitFunctor % Nat (Next f) (Next g) (n . OS))


instance (Functor f, Dom f ~ Discrete Z, HasInitialObject (Cod f)) => HasColimit (Discrete Z) f where

  type Colimit (Discrete Z) f = InitialObject (Cod f)

  colimit f = Nat f (Const initialObject) magicZO
  
  colimitFactorizer _ = initialize . coconeVertex
  
instance (Functor f, Dom f ~ Discrete (S n), HasCoproducts (Cod f), Category (Discrete n), HasColimit (Discrete n) (Next n f)) 
  => HasColimit (Discrete (S n)) f where
    
  type Colimit (Discrete (S n)) f = Coproduct (Cod f) (f :% Z) (Colimit (Discrete n) (Next n f))

  colimit f = undefined -- diagNat (Const cop) f (Com . fst $ i) (Com . snd $ i)
    where
      x = (f %% OZ)
      cocone = colimit (Next f)
      y = coconeVertex cocone
      cop = coproduct x y
      i = inj x y
      
  -- colimitFactorizer _ (Cocone _ (Nat f g n)) = (n OZ) ||| (colimitFactorizer undefined (Cocone undefined $  Nat (Next f) (Next g) (n . OS)))



newtype ForAll f = ForAll { unForAll :: forall a. f a }

instance HasLimit (->) (EndoHask f) where
  
  type Limit (->) (EndoHask f) = ForAll f

  limit EndoHask = Nat (Const HaskO) EndoHask $ \HaskO -> unForAll
  
  limitFactorizer EndoHask c n = ForAll ((c ! HaskO) n)


data Exists f = forall a. Exists { unExists :: f a }

instance HasColimit (->) (EndoHask f) where
  
  type Colimit (->) (EndoHask f) = Exists f
  
  colimit EndoHask = Nat EndoHask (Const HaskO) $ \HaskO -> Exists
  
  colimitFactorizer EndoHask c (Exists fa) = (c ! HaskO) fa
