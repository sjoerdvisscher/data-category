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
type instance F (Diag j (~>)) a = Const j (~>) a

instance Functor (Diag j (~>)) where 
  Diag %% x = NatO $ Const x
  Diag %  f = Nat (Const $ src f) (Const $ tgt f) $ const f

type DiagF f = Diag (Dom f) (Cod f)



-- | A cone from N to F is a natural transformation from the constant functor to N to F.
data Cone   f n = Cone
  { coneVertex  :: Obj (Cod f) n
  , coneSurface :: Nat (Dom f) (Cod f) (ConstF f n) f
  }

-- | A co-cone from F to N is a natural transformation from F to the constant functor to N.
data Cocone f n = Cocone
  { coconeVertex  :: Obj (Cod f) n
  , coconeSurface :: Nat (Dom f) (Cod f) f (ConstF f n)
  }



type family Limit j f :: *  

class (Category j, Category (~>)) => HasLimits j (~>) where
  
  limitUniversal :: (Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> TerminalUniversal f (Diag j (~>)) (Limit j f)
  limitUniversal f = let l = limit f in TerminalUniversal
    { tuObject           = coneVertex l
    , terminalMorphism   = coneSurface l
    , terminalFactorizer = \v s -> limitFactorizer f (Cone v s)
    }
  
  limit :: (Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> Cone f (Limit j f)
  limit f = let u = limitUniversal f in Cone
    { coneVertex  = tuObject u
    , coneSurface = terminalMorphism u }
  
  limitFactorizer :: (Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> Cone f n -> Cod f n (Limit j f)
  limitFactorizer f (Cone v s) = terminalFactorizer (limitUniversal f) v s


type family Colimit j f :: *

class (Category j, Category (~>)) => HasColimits j (~>) where
  
  colimitUniversal :: (Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> InitialUniversal f (DiagF f) (Colimit j f)
  colimitUniversal f = let l = colimit f in InitialUniversal
    { iuObject          = coconeVertex l
    , initialMorphism   = coconeSurface l
    , initialFactorizer = \v s -> colimitFactorizer f (Cocone v s)
    }
  
  colimit :: (Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> Cocone f (Colimit j f)
  colimit f = let u = colimitUniversal f in Cocone
    { coconeVertex  = iuObject u
    , coconeSurface = initialMorphism u }
    
  colimitFactorizer :: (Dom f ~ j, Cod f ~ (~>)) => Obj (Nat j (~>)) f -> Cocone f n -> Cod f (Colimit j f) n
  colimitFactorizer f (Cocone v s) = initialFactorizer (colimitUniversal f) v s



data LimitFunctor :: (* -> * -> *) -> (* -> * -> *) -> * where
  LimitFunctor :: HasLimits j (~>) => LimitFunctor j (~>)

type instance Dom (LimitFunctor j (~>)) = Nat j (~>)
type instance Cod (LimitFunctor j (~>)) = (~>)
type instance F (LimitFunctor j (~>)) f = Limit j f

instance Functor (LimitFunctor j (~>)) where
  LimitFunctor %% NatO f     = coneVertex (limit (NatO f))
  LimitFunctor % (Nat f g n) = undefined

    
data ColimitFunctor :: (* -> * -> *) -> (* -> * -> *) -> * where
  ColimitFunctor :: HasColimits j (~>) => ColimitFunctor j (~>)
  
type instance Dom (ColimitFunctor j (~>)) = Nat j (~>)
type instance Cod (ColimitFunctor j (~>)) = (~>)
type instance F (ColimitFunctor j (~>)) f = Colimit j f

instance Functor (ColimitFunctor j (~>)) where
  ColimitFunctor %% NatO f     = coconeVertex (colimit (NatO f))
  ColimitFunctor % (Nat f g n) = undefined


-- | A terminal object is the limit of the functor from /0/ to (~>).
class Category (~>) => HasTerminalObject (~>) where
  
  type TerminalObject (~>) :: *
  
  terminalObject :: Obj (~>) (TerminalObject (~>))
  
  terminate :: Obj (~>) a -> a ~> TerminalObject (~>)


type instance Limit Void f = TerminalObject (Cod f)

instance (HasTerminalObject (~>)) => HasLimits Void (~>) where
  
  limit (NatO f) = Cone terminalObject $ voidNat (Const terminalObject) f
  
  limitFactorizer _ (Cone n _) = terminate n


instance HasTerminalObject (->) where
  
  type TerminalObject (->) = ()
  
  terminalObject = HaskO
  
  terminate HaskO _ = ()

instance HasTerminalObject Cat where
  
  type TerminalObject Cat = CatW Unit
  
  terminalObject = CatO
  
  terminate CatO = CatA $ Const UnitO


-- | An initial object is the colimit of the functor from /0/ to (~>).
class Category (~>) => HasInitialObject (~>) where
  
  type InitialObject (~>) :: *
  
  initialObject :: Obj (~>) (InitialObject (~>))

  initialize :: Obj (~>) a -> InitialObject (~>) ~> a


type instance Colimit Void f = InitialObject (Cod f)

instance (HasInitialObject (~>)) => HasColimits Void (~>) where
  
  colimit (NatO f) = Cocone initialObject $ voidNat f (Const initialObject)
  
  colimitFactorizer _ (Cocone n _) = initialize n


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


type instance Limit Pair f = Product (Cod f) (F f P1) (F f P2)

instance (HasProducts (~>)) => HasLimits Pair (~>) where
  
  limit (NatO f) = Cone prod $ pairNat (Const prod) f (Com . fst $ prj) (Com . snd $ prj)
    where
      x = f %% Fst
      y = f %% Snd
      prod = product x y
      prj = proj x y
  
  limitFactorizer _ (Cone _ s) = (s ! Fst) &&& (s ! Snd)


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
    

type instance Colimit Pair f = Coproduct (Cod f) (F f P1) (F f P2)

instance (HasCoproducts (~>)) => HasColimits Pair (~>) where
  
  colimit (NatO f) = Cocone cop $ pairNat f (Const cop) (Com . fst $ i) (Com . snd $ i)
    where
      x = f %% Fst
      y = f %% Snd
      cop = coproduct x y
      i = inj x y
  
  colimitFactorizer _ (Cocone _ s) = (s ! Fst) ||| (s ! Snd)


type instance Coproduct (->) x y = Either x y

instance HasCoproducts (->) where
  
  coproduct HaskO HaskO = HaskO
  
  inj _ _ = (Left, Right)
  
  (|||) = (A.|||)
  (+++) = (A.+++)


type instance Limit (Discrete Z) f = TerminalObject (Cod f)
type instance Limit (Discrete (S n)) f = Product (Cod f) (F f Z) (Limit (Discrete n) (Next n f))

instance HasTerminalObject (~>) => HasLimits (Discrete Z) (~>) where

  limit (NatO f) = Cone terminalObject $ Nat (Const terminalObject) f magicZO
  
  limitFactorizer _ (Cone n _) = terminate n
  
instance (HasProducts (~>), Category (Discrete n), HasLimits (Discrete n) (~>)) 
  => HasLimits (Discrete (S n)) (~>) where
    
  limit (NatO f) = Cone prod undefined -- diagNat (Const prod) f (Com . fst $ prj) (Com . snd $ prj)
    where
      x = (f %% OZ)
      Cone y ns = limit (NatO $ Next f)
      prod = product x y
      prj = proj x y
      
  -- LimitFunctor % Nat f g n = n OZ      ***       (LimitFunctor % Nat (Next f) (Next g) (n . OS))


type instance Colimit (Discrete Z) f = InitialObject (Cod f)
type instance Colimit (Discrete (S n)) f = Coproduct (Cod f) (F f Z) (Colimit (Discrete n) (Next n f))

instance HasInitialObject (~>) => HasColimits (Discrete Z) (~>) where

  colimit (NatO f) = Cocone initialObject $ Nat f (Const initialObject) magicZO
  
  colimitFactorizer _ (Cocone n _) = initialize n
  
instance (HasCoproducts (~>), Category (Discrete n), HasColimits (Discrete n) (~>)) 
  => HasColimits (Discrete (S n)) (~>) where
    
  colimit (NatO f) = Cocone cop undefined -- diagNat (Const cop) f (Com . fst $ i) (Com . snd $ i)
    where
      x = (f %% OZ)
      Cocone y ns = colimit (NatO $ Next f)
      cop = coproduct x y
      i = inj x y
      
  -- colimitFactorizer _ (Cocone _ (Nat f g n)) = (n OZ) ||| (colimitFactorizer undefined (Cocone undefined $  Nat (Next f) (Next g) (n . OS)))
