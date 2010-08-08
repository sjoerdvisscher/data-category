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
module Data.Category.Limit (

  -- * Prelimiairies
  
  -- ** Diagonal Functor
    Diag(..)
  , DiagF
  
  -- ** Cones
  , Cone
  , Cocone
  , coneVertex
  , coconeVertex
  
  -- * Limits
  , LimitFam
  , Limit
  , LimitUniversal
  , limitUniversal
  , limit
  , limitFactorizer
  
  -- * Colimits
  , ColimitFam
  , Colimit
  , ColimitUniversal
  , colimitUniversal
  , colimit
  , colimitFactorizer
  
  -- * Limits of a certain type
  , HasLimits(..)
  , HasColimits(..)
  
  -- ** As a functor
  , LimitFunctor(..)
  , ColimitFunctor(..)
  
  -- ** Limits of type Void
  , HasTerminalObject(..)
  , HasInitialObject(..)
  , Zero
  
  -- ** Limits of type Pair
  , BinaryProduct
  , HasBinaryProducts(..)
  , (:*:)
  , BinaryCoproduct
  , HasBinaryCoproducts(..)
  , (:+:)
  
  -- ** Limits of type Hask
  , ForAll(..)
  , endoHaskLimit
  , Exists(..)
  , endoHaskColimit
  
) where

import Prelude hiding ((.), id, Functor, product)
import qualified Prelude (Functor)
import qualified Control.Arrow as A ((&&&), (***), (|||), (+++))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Void
import Data.Category.Pair
import Data.Category.Unit
import Data.Category.Product
import Data.Category.Discrete

infixr 3 ***
infixr 3 &&&
infixr 2 +++
infixr 2 |||


-- | The diagonal functor from (index-) category J to (~>).
data Diag :: (* -> * -> *) -> (* -> * -> *) -> * where
  Diag :: (Category j, Category (~>)) => Diag j (~>)
  
type instance Dom (Diag j (~>)) = (~>)
type instance Cod (Diag j (~>)) = Nat j (~>)
type instance Diag j (~>) :% a = Const j (~>) a

instance Functor (Diag j (~>)) where 
  Diag %% x = NatO $ Const x
  Diag %  f = Nat (Const $ src f) (Const $ tgt f) $ const f

-- | The diagonal functor with the same domain and codomain as @f@.
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
type family LimitFam j (~>) f :: *

type Limit f = LimitFam (Dom f) (Cod f) f

-- | A limit of @f@ is a universal morphism from the diagonal functor to @f@.
type LimitUniversal f = TerminalUniversal f (DiagF f) (Limit f)

-- | @limitUniversal@ is a helper function to create the universal property from the limit and the limit factorizer.
limitUniversal :: (Cod f ~ (~>)) 
  => Cone f (Limit f)
  -> (forall n. Cone f n -> n ~> Limit f)
  -> LimitUniversal f
limitUniversal l lf = TerminalUniversal
  { tuObject           = coneVertex l
  , terminalMorphism   = l
  , terminalFactorizer = const lf
  }

-- | A limit of the diagram @f@ is a cone of @f@.
limit :: LimitUniversal f -> Cone f (Limit f)
limit = terminalMorphism

-- | For any other cone of @f@ with vertex @n@ there exists a unique morphism from @n@ to the limit of @f@.
limitFactorizer :: (Cod f ~ (~>)) => LimitUniversal f -> (forall n. Cone f n -> n ~> Limit f)
limitFactorizer lu c = terminalFactorizer lu (coneVertex c) c



-- | Colimits in a category @(~>)@ by means of a diagram of type @j@, which is a functor from @j@ to @(~>)@.
type family ColimitFam j (~>) f :: *

type Colimit f = ColimitFam (Dom f) (Cod f) f

-- | A colimit of @f@ is a universal morphism from @f@ to the diagonal functor.
type ColimitUniversal f = InitialUniversal f (DiagF f) (Colimit f)

-- | @colimitUniversal@ is a helper function to create the universal property from the colimit and the colimit factorizer.
colimitUniversal :: (Cod f ~ (~>)) 
  => Cocone f (Colimit f)
  -> (forall n. Cocone f n -> Colimit f ~> n)
  -> ColimitUniversal f
colimitUniversal l lf = InitialUniversal
  { iuObject          = coconeVertex l
  , initialMorphism   = l
  , initialFactorizer = const lf
  }

-- | A colimit of the diagram @f@ is a co-cone of @f@.
colimit :: ColimitUniversal f -> Cocone f (Colimit f)
colimit = initialMorphism

-- | For any other co-cone of @f@ with vertex @n@ there exists a unique morphism from the colimit of @f@ to @n@.
colimitFactorizer :: (Cod f ~ (~>)) => ColimitUniversal f -> (forall n. Cocone f n -> Colimit f ~> n)
colimitFactorizer cu c = initialFactorizer cu (coconeVertex c) c



-- | An instance of @HasLimits j (~>)@ says that @(~>)@ has all limits of type @j@.
class (Category j, Category (~>)) => HasLimits j (~>) where
  limitUniv :: Obj (Nat j (~>)) f -> LimitUniversal f

-- | If every diagram of type @j@ has a limit in @(~>)@ there exists a limit functor.
--
--   Applied to a natural transformation it is a generalisation of @(***)@:
--
--   @l@ '***' @r =@ 'LimitFunctor' '%' 'arrowPair' @l r@
data LimitFunctor :: (* -> * -> *) -> (* -> * -> *) -> * where
  LimitFunctor :: HasLimits j (~>) => LimitFunctor j (~>)

type instance Dom (LimitFunctor j (~>)) = Nat j (~>)
type instance Cod (LimitFunctor j (~>)) = (~>)
type instance LimitFunctor j (~>) :% f = LimitFam j (~>) f

instance Functor (LimitFunctor j (~>)) where
  LimitFunctor %% f @ NatO{} = tuObject (limitUniv f)
  LimitFunctor %  n @ Nat{}  = limitFactorizer (limitUniv (tgt n)) (n . limit (limitUniv (src n)))



-- | An instance of @HasColimits j (~>)@ says that @(~>)@ has all colimits of type @j@.
class (Category j, Category (~>)) => HasColimits j (~>) where
  colimitUniv :: Obj (Nat j (~>)) f -> ColimitUniversal f

-- | If every diagram of type @j@ has a colimit in @(~>)@ there exists a colimit functor.
--
--   Applied to a natural transformation it is a generalisation of @(+++)@:
--
--   @l@ '+++' @r =@ 'ColimitFunctor' '%' 'arrowPair' @l r@
data ColimitFunctor :: (* -> * -> *) -> (* -> * -> *) -> * where
  ColimitFunctor :: HasColimits j (~>) => ColimitFunctor j (~>)
  
type instance Dom (ColimitFunctor j (~>)) = Nat j (~>)
type instance Cod (ColimitFunctor j (~>)) = (~>)
type instance ColimitFunctor j (~>) :% f = ColimitFam j (~>) f

instance Functor (ColimitFunctor j (~>)) where
  ColimitFunctor %% f @ NatO{} = iuObject (colimitUniv f)
  ColimitFunctor %  n @ Nat{}  = colimitFactorizer (colimitUniv (src n)) (colimit (colimitUniv (tgt n)) . n)



-- | A terminal object is the limit of the functor from /0/ to (~>).
class Category (~>) => HasTerminalObject (~>) where
  
  type TerminalObject (~>) :: *
  
  terminalObject :: Obj (~>) (TerminalObject (~>))
  
  terminate :: Obj (~>) a -> a ~> TerminalObject (~>)


type instance LimitFam Void (~>) f = TerminalObject (~>)

instance (HasTerminalObject (~>)) => HasLimits Void (~>) where
  
  limitUniv (NatO f) = limitUniversal
    (voidNat (Const terminalObject) f)
    (terminate . coneVertex)


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


type instance ColimitFam Void (~>) f = InitialObject (~>)

instance HasInitialObject (~>) => HasColimits Void (~>) where
  
  colimitUniv (NatO f) = colimitUniversal
    (voidNat f (Const initialObject))
    (initialize . coconeVertex)


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



type family BinaryProduct ((~>) :: * -> * -> *) x y :: *

-- | The product of 2 objects is the limit of the functor from Pair to (~>).
class Category (~>) => HasBinaryProducts (~>) where
  
  product :: Obj (~>) x -> Obj (~>) y -> Obj (~>) (BinaryProduct (~>) x y)
  
  proj1 :: Obj (~>) x -> Obj (~>) y -> BinaryProduct (~>) x y ~> x
  proj2 :: Obj (~>) x -> Obj (~>) y -> BinaryProduct (~>) x y ~> y

  (&&&) :: (a ~> x) -> (a ~> y) -> (a ~> BinaryProduct (~>) x y)

  (***) :: (a1 ~> b1) -> (a2 ~> b2) -> (BinaryProduct (~>) a1 a2 ~> BinaryProduct (~>) b1 b2)
  l *** r = (l . proj1 (src l) (src r)) &&& (r . proj2 (src l) (src r)) where


type instance LimitFam Pair (~>) f = BinaryProduct (~>) (f :% P1) (f :% P2)

instance HasBinaryProducts (~>) => HasLimits Pair (~>) where

  limitUniv (NatO f) = limitUniversal
    (pairNat (Const $ product x y) f (Com $ proj1 x y) (Com $ proj2 x y))
    (\c -> c ! Fst &&& c ! Snd)
    where
      x = f %% Fst
      y = f %% Snd


type instance BinaryProduct (->) x y = (x, y)

instance HasBinaryProducts (->) where
  
  product HaskO HaskO = HaskO
  
  proj1 HaskO HaskO = fst
  proj2 HaskO HaskO = snd
  
  (&&&) = (A.&&&)
  (***) = (A.***)

type instance BinaryProduct Cat (CatW c1) (CatW c2) = CatW (c1 :**: c2)

instance HasBinaryProducts Cat where
  
  product CatO CatO = CatO
  
  proj1 CatO CatO = CatA Proj1
  proj2 CatO CatO = CatA Proj2
  
  CatA f1 &&& CatA f2 = CatA ((f1 :***: f2) :.: DiagProd)
  CatA f1 *** CatA f2 = CatA (f1 :***: f2)


type instance BinaryProduct (c1 :**: c2) (x1, x2) (y1, y2) = (BinaryProduct c1 x1 y1, BinaryProduct c2 x2 y2)

instance (HasBinaryProducts c1, HasBinaryProducts c2) => HasBinaryProducts (c1 :**: c2) where
  
  product (ProdO x1 x2) (ProdO y1 y2) = ProdO (product x1 y1) (product x2 y2)
  
  proj1 (ProdO x1 x2) (ProdO y1 y2) = proj1 x1 y1 :**: proj1 x2 y2
  proj2 (ProdO x1 x2) (ProdO y1 y2) = proj2 x1 y1 :**: proj2 x2 y2
  
  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)
  (f1 :**: f2) *** (g1 :**: g2) = (f1 *** g1) :**: (f2 *** g2)


-- | The product of two functors.
data p :*: q where 
  (:*:) :: (Functor p, Functor q, Dom p ~ Dom q, Cod p ~ (~>), Cod q ~ (~>), HasBinaryProducts (~>)) => p -> q -> p :*: q
type instance Dom (p :*: q) = Dom p
type instance Cod (p :*: q) = Cod p
type instance (p :*: q) :% a = BinaryProduct (Cod p) (p :% a) (q :% a)
instance Functor (p :*: q) where
  (p :*: q) %% a = (p %% a) `product` (q %% a)
  (p :*: q) %  f = (p %  f)  ***      (q %  f)

type instance BinaryProduct (Nat c d) x y = x :*: y

instance (Category c, HasBinaryProducts d) => HasBinaryProducts (Nat c d) where
  
  product (NatO f) (NatO g) = NatO (f :*: g)
  
  proj1 (NatO f) (NatO g) = Nat (f :*: g) f $ \z -> proj1 (f %% z) (g %% z)
  proj2 (NatO f) (NatO g) = Nat (f :*: g) g $ \z -> proj2 (f %% z) (g %% z)
  
  Nat a f af &&& Nat _ g ag = Nat a (f :*: g) $ \z -> af z &&& ag z
  Nat f1 f2 f *** Nat g1 g2 g = Nat (f1 :*: g1) (f2 :*: g2) $ \z -> f z *** g z
  
  

type family BinaryCoproduct ((~>) :: * -> * -> *) x y :: *

-- | The coproduct of 2 objects is the colimit of the functor from Pair to (~>).
class Category (~>) => HasBinaryCoproducts (~>) where

  coproduct :: Obj (~>) x -> Obj (~>) y -> Obj (~>) (BinaryCoproduct (~>) x y)
  
  inj1 :: Obj (~>) x -> Obj (~>) y -> x ~> BinaryCoproduct (~>) x y
  inj2 :: Obj (~>) x -> Obj (~>) y -> y ~> BinaryCoproduct (~>) x y

  (|||) :: (x ~> a) -> (y ~> a) -> (BinaryCoproduct (~>) x y ~> a)
    
  (+++) :: (a1 ~> b1) -> (a2 ~> b2) -> (BinaryCoproduct (~>) a1 a2 ~> BinaryCoproduct (~>) b1 b2)
  l +++ r = (inj1 (tgt l) (tgt r) . l) ||| (inj2 (tgt l) (tgt r) . r) where
    

type instance ColimitFam Pair (~>) f = BinaryCoproduct (~>) (f :% P1) (f :% P2)

instance HasBinaryCoproducts (~>) => HasColimits Pair (~>) where
  
  colimitUniv (NatO f) = colimitUniversal
    (pairNat f (Const $ coproduct x y) (Com $ inj1 x y) (Com $ inj2 x y))
    (\c -> c ! Fst ||| c ! Snd)
    where
      x = f %% Fst
      y = f %% Snd


type instance BinaryCoproduct (->) x y = Either x y

instance HasBinaryCoproducts (->) where
  
  coproduct HaskO HaskO = HaskO
  
  inj1 HaskO HaskO = Left
  inj2 HaskO HaskO = Right
  
  (|||) = (A.|||)
  (+++) = (A.+++)
  
  
type instance BinaryCoproduct (c1 :**: c2) (x1, x2) (y1, y2) = (BinaryCoproduct c1 x1 y1, BinaryCoproduct c2 x2 y2)

instance (HasBinaryCoproducts c1, HasBinaryCoproducts c2) => HasBinaryCoproducts (c1 :**: c2) where
  
  coproduct (ProdO x1 x2) (ProdO y1 y2) = ProdO (coproduct x1 y1) (coproduct x2 y2)
  
  inj1 (ProdO x1 x2) (ProdO y1 y2) = inj1 x1 y1 :**: inj1 x2 y2
  inj2 (ProdO x1 x2) (ProdO y1 y2) = inj2 x1 y1 :**: inj2 x2 y2
  
  (f1 :**: f2) ||| (g1 :**: g2) = (f1 ||| g1) :**: (f2 ||| g2)
  (f1 :**: f2) +++ (g1 :**: g2) = (f1 +++ g1) :**: (f2 +++ g2)


-- | The coproduct of two functors.
data p :+: q where 
  (:+:) :: (Functor p, Functor q, Dom p ~ Dom q, Cod p ~ (~>), Cod q ~ (~>), HasBinaryCoproducts (~>)) => p -> q -> p :+: q
type instance Dom (p :+: q) = Dom p
type instance Cod (p :+: q) = Cod p
type instance (p :+: q) :% a = BinaryCoproduct (Cod p) (p :% a) (q :% a)
instance Functor (p :+: q) where
  (p :+: q) %% a = (p %% a) `coproduct` (q %% a)
  (p :+: q) %  f = (p %  f)  +++        (q %  f)

type instance BinaryCoproduct (Nat c d) x y = x :+: y

instance (Category c, HasBinaryCoproducts d) => HasBinaryCoproducts (Nat c d) where
  
  coproduct (NatO f) (NatO g) = NatO (f :+: g)
  
  inj1 (NatO f) (NatO g) = Nat f (f :+: g) $ \z -> inj1 (f %% z) (g %% z)
  inj2 (NatO f) (NatO g) = Nat g (f :+: g) $ \z -> inj2 (f %% z) (g %% z)
  
  Nat f a fa ||| Nat g _ ga = Nat (f :+: g) a $ \z -> fa z ||| ga z
  Nat f1 f2 f +++ Nat g1 g2 g = Nat (f1 :+: g1) (f2 :+: g2) $ \z -> f z +++ g z



newtype ForAll f = ForAll { unForAll :: forall a. f a }

type instance LimitFam (->) (->) (EndoHask f) = ForAll f

endoHaskLimit :: Prelude.Functor f => LimitUniversal (EndoHask f)
endoHaskLimit = limitUniversal
  (Nat (Const HaskO) EndoHask $ \HaskO -> unForAll)
  (\c n -> ForAll ((c ! HaskO) n)) -- ForAll . (c ! Hask)


data Exists f = forall a. Exists (f a)

type instance ColimitFam (->) (->) (EndoHask f) = Exists f

endoHaskColimit :: Prelude.Functor f => ColimitUniversal (EndoHask f)
endoHaskColimit = colimitUniversal
  (Nat EndoHask (Const HaskO) $ \HaskO -> Exists)
  (\c (Exists fa) -> (c ! HaskO) fa) -- (c ! HaskO) . unExists
