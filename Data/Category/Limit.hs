{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  GADTs,
  PolyKinds,
  DataKinds,
  MultiParamTypeClasses,
  RankNTypes,
  ScopedTypeVariables,
  TypeOperators,
  TypeFamilies,
  TypeSynonymInstances,
  UndecidableInstances,
  NoImplicitPrelude  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Limit
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Limit (

  -- * Preliminairies

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
  , HasLimits(..)
  , LimitFunctor(..)
  , limitAdj
  , rightAdjointPreservesLimits
  , rightAdjointPreservesLimitsInv

  -- * Colimits
  , ColimitFam
  , Colimit
  , HasColimits(..)
  , ColimitFunctor(..)
  , colimitAdj
  , leftAdjointPreservesColimits
  , leftAdjointPreservesColimitsInv

  -- ** Limits of type Void
  , HasTerminalObject(..)
  , HasInitialObject(..)
  , Zero

  -- ** Limits of type Pair
  , HasBinaryProducts(..)
  , ProductFunctor(..)
  , (:*:)(..)
  , prodAdj
  , HasBinaryCoproducts(..)
  , CoproductFunctor(..)
  , (:+:)(..)
  , coprodAdj

) where

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction

import Data.Category.Product
import Data.Category.Coproduct
import Data.Category.Unit
import Data.Category.Void

infixl 3 ***
infixl 3 &&&
infixl 2 +++
infixl 2 |||


data Diag :: (* -> * -> *) -> (* -> * -> *) -> * where
  Diag :: Diag j k

-- | The diagonal functor from (index-) category J to k.
instance (Category j, Category k) => Functor (Diag j k) where
  type Dom (Diag j k) = k
  type Cod (Diag j k) = Nat j k
  type Diag j k :% a = Const j k a

  Diag % f = Nat (Const (src f)) (Const (tgt f)) (\_ -> f)

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



-- | Limits in a category @k@ by means of a diagram of type @j@, which is a functor from @j@ to @k@.
type family LimitFam (j :: * -> * -> *) (k :: * -> * -> *) (f :: *) :: *

type Limit f = LimitFam (Dom f) (Cod f) f

-- | An instance of @HasLimits j k@ says that @k@ has all limits of type @j@.
class (Category j, Category k) => HasLimits j k where
  -- | 'limit' returns the limiting cone for a functor @f@.
  limit           :: Obj (Nat j k) f -> Cone f (Limit f)
  -- | 'limitFactorizer' shows that the limiting cone is universal – i.e. any other cone of @f@ factors through it
  --   by returning the morphism between the vertices of the cones.
  limitFactorizer :: Obj (Nat j k) f -> Cone f n -> k n (Limit f)

data LimitFunctor (j :: * -> * -> *) (k  :: * -> * -> *) = LimitFunctor
-- | If every diagram of type @j@ has a limit in @k@ there exists a limit functor.
--   It can be seen as a generalisation of @(***)@.
instance HasLimits j k => Functor (LimitFunctor j k) where
  type Dom (LimitFunctor j k) = Nat j k
  type Cod (LimitFunctor j k) = k
  type LimitFunctor j k :% f = LimitFam j k f

  LimitFunctor % n @ Nat{}  = limitFactorizer (tgt n) (n . limit (src n))

-- | The limit functor is right adjoint to the diagonal functor.
limitAdj :: forall j k. HasLimits j k => Adjunction (Nat j k) k (Diag j k) (LimitFunctor j k)
limitAdj = mkAdjunctionUnits diag LimitFunctor (\a -> limitFactorizer (diag % a) (diag % a)) (\f @ Nat{} -> limit f)
  where diag = Diag :: Diag j k -- Forces the type of all Diags to be the same.

-- Cone (g :.: t) (Limit (g :.: t))
-- Obj j z -> d (Limit (g :.: t)) ((g :.: t) :% z)
-- Obj j z -> d (f :% Limit (g :.: t)) (t :% z)
-- Cone t (f :% Limit (g :.: t))
-- d (f :% Limit (g :.: t)) (Limit t)
-- d (Limit (g :.: t)) (g :% Limit t)
rightAdjointPreservesLimits
  :: (HasLimits j c, HasLimits j d)
  => Adjunction c d f g -> Obj (Nat j c) t -> d (Limit (g :.: t)) (g :% Limit t)
rightAdjointPreservesLimits adj@(Adjunction f g _ _) (Nat t _ _) =
  leftAdjunct adj x (limitFactorizer (natId t) cone)
    where
      l = limit (natId (g :.: t))
      x = coneVertex l
      -- cone :: Cone t (f :% Limit (g :.: t))
      cone = Nat (Const (f % x)) t (\z -> rightAdjunct adj (t % z) (l ! z))

-- Cone t (Limit t)
-- Cone (g :.: t) (g :% Limit t)
-- d (g :% Limit t) (Limit (g :.: t))
rightAdjointPreservesLimitsInv
  :: (HasLimits j c, HasLimits j d)
  => Obj (Nat c d) g -> Obj (Nat j c) t -> d (g :% Limit t) (Limit (g :.: t))
rightAdjointPreservesLimitsInv g@Nat{} t@Nat{} = limitFactorizer (g `o` t) (constPrecompIn (g `o` limit t))

-- | Colimits in a category @k@ by means of a diagram of type @j@, which is a functor from @j@ to @k@.
type family ColimitFam (j :: * -> * -> *) (k :: * -> * -> *) (f :: *) :: *

type Colimit f = ColimitFam (Dom f) (Cod f) f

-- | An instance of @HasColimits j k@ says that @k@ has all colimits of type @j@.
class (Category j, Category k) => HasColimits j k where
  -- | 'colimit' returns the limiting co-cone for a functor @f@.
  colimit           :: Obj (Nat j k) f -> Cocone f (Colimit f)
  -- | 'colimitFactorizer' shows that the limiting co-cone is universal – i.e. any other co-cone of @f@ factors through it
  --   by returning the morphism between the vertices of the cones.
  colimitFactorizer :: Obj (Nat j k) f -> Cocone f n -> k (Colimit f) n

data ColimitFunctor (j :: * -> * -> *) (k  :: * -> * -> *) = ColimitFunctor
-- | If every diagram of type @j@ has a colimit in @k@ there exists a colimit functor.
--   It can be seen as a generalisation of @(+++)@.
instance HasColimits j k => Functor (ColimitFunctor j k) where
  type Dom (ColimitFunctor j k) = Nat j k
  type Cod (ColimitFunctor j k) = k
  type ColimitFunctor j k :% f = ColimitFam j k f

  ColimitFunctor % n @ Nat{}  = colimitFactorizer (src n) (colimit (tgt n) . n)

-- | The colimit functor is left adjoint to the diagonal functor.
colimitAdj :: forall j k. HasColimits j k => Adjunction k (Nat j k) (ColimitFunctor j k) (Diag j k)
colimitAdj = mkAdjunctionUnits ColimitFunctor diag (\f @ Nat{} -> colimit f) (\a -> colimitFactorizer (diag % a) (diag % a))
  where diag = Diag :: Diag j k -- Forces the type of all Diags to be the same.


leftAdjointPreservesColimits
  :: (HasColimits j c, HasColimits j d)
  => Adjunction c d f g -> Obj (Nat j d) t -> c (f :% Colimit t) (Colimit (f :.: t))
leftAdjointPreservesColimits adj@(Adjunction f g _ _) (Nat t _ _) =
  rightAdjunct adj x (colimitFactorizer (natId t) cocone)
    where
      l = colimit (natId (f :.: t))
      x = coconeVertex l
      cocone = Nat t (Const (g % x)) (\z -> leftAdjunct adj (t % z) (l ! z))

leftAdjointPreservesColimitsInv
  :: (HasColimits j c, HasColimits j d)
  => Obj (Nat d c) f -> Obj (Nat j d) t -> c (Colimit (f :.: t)) (f :% Colimit t)
leftAdjointPreservesColimitsInv f@Nat{} t@Nat{} = colimitFactorizer (f `o` t) (constPrecompOut (f `o` colimit t))


class Category k => HasTerminalObject k where

  type TerminalObject k :: Kind k

  terminalObject :: Obj k (TerminalObject k)

  terminate :: Obj k a -> k a (TerminalObject k)


type instance LimitFam Void k f = TerminalObject k

-- | A terminal object is the limit of the functor from /0/ to k.
instance (Category k, HasTerminalObject k) => HasLimits Void k where

  limit (Nat f _ _) = voidNat (Const terminalObject) f
  limitFactorizer Nat{} = terminate . coneVertex


-- | @()@ is the terminal object in @Hask@.
instance HasTerminalObject (->) where
  type TerminalObject (->) = ()

  terminalObject = \x -> x

  terminate _ _ = ()

-- | @Unit@ is the terminal category.
instance HasTerminalObject Cat where
  type TerminalObject Cat = Unit

  terminalObject = CatA Id

  terminate (CatA _) = CatA (Const Unit)

-- | The constant functor to the terminal object is itself the terminal object in its functor category.
instance (Category c, HasTerminalObject d) => HasTerminalObject (Nat c d) where
  type TerminalObject (Nat c d) = Const c d (TerminalObject d)

  terminalObject = natId (Const terminalObject)

  terminate (Nat f _ _) = Nat f (Const terminalObject) (terminate . (f %))

-- | The category of one object has that object as terminal object.
instance HasTerminalObject Unit where
  type TerminalObject Unit = ()

  terminalObject = Unit

  terminate Unit = Unit

-- | The terminal object of the product of 2 categories is the product of their terminal objects.
instance (HasTerminalObject c1, HasTerminalObject c2) => HasTerminalObject (c1 :**: c2) where
  type TerminalObject (c1 :**: c2) = (TerminalObject c1, TerminalObject c2)

  terminalObject = terminalObject :**: terminalObject

  terminate (a1 :**: a2) = terminate a1 :**: terminate a2

-- | The terminal object of the direct coproduct of categories is the terminal object of the terminal category.
instance (Category c1, HasTerminalObject c2) => HasTerminalObject (c1 :>>: c2) where
  type TerminalObject (c1 :>>: c2) = I2 (TerminalObject c2)

  terminalObject = DC (I2A terminalObject)

  terminate (DC (I1A a)) = DC (I12 a terminalObject (Const (\() -> ())) ())
  terminate (DC (I2A a)) = DC (I2A (terminate a))



class Category k => HasInitialObject k where
  type InitialObject k :: Kind k

  initialObject :: Obj k (InitialObject k)

  initialize :: Obj k a -> k (InitialObject k) a


type instance ColimitFam Void k f = InitialObject k

-- | An initial object is the colimit of the functor from /0/ to k.
instance (Category k, HasInitialObject k) => HasColimits Void k where

  colimit (Nat f _ _) = voidNat f (Const initialObject)
  colimitFactorizer Nat{} = initialize . coconeVertex


data Zero

-- | Any empty data type is an initial object in @Hask@.
instance HasInitialObject (->) where
  type InitialObject (->) = Zero

  initialObject = \x -> x

  initialize = initialize

-- | The empty category is the initial object in @Cat@.
instance HasInitialObject Cat where
  type InitialObject Cat = Void

  initialObject = CatA Id

  initialize (CatA _) = CatA Magic

-- | The constant functor to the initial object is itself the initial object in its functor category.
instance (Category c, HasInitialObject d) => HasInitialObject (Nat c d) where
  type InitialObject (Nat c d) = Const c d (InitialObject d)

  initialObject = natId (Const initialObject)

  initialize (Nat f _ _) = Nat (Const initialObject) f (initialize . (f %))

-- | The initial object of the product of 2 categories is the product of their initial objects.
instance (HasInitialObject c1, HasInitialObject c2) => HasInitialObject (c1 :**: c2) where
  type InitialObject (c1 :**: c2) = (InitialObject c1, InitialObject c2)

  initialObject = initialObject :**: initialObject

  initialize (a1 :**: a2) = initialize a1 :**: initialize a2

-- | The category of one object has that object as initial object.
instance HasInitialObject Unit where
  type InitialObject Unit = ()

  initialObject = Unit

  initialize Unit = Unit

-- | The initial object of the direct coproduct of categories is the initial object of the initial category.
instance (HasInitialObject c1, Category c2) => HasInitialObject (c1 :>>: c2) where
  type InitialObject (c1 :>>: c2) = I1 (InitialObject c1)

  initialObject = DC (I1A initialObject)

  initialize (DC (I1A a)) = DC (I1A (initialize a))
  initialize (DC (I2A a)) = DC (I12 initialObject a (Const (\() -> ())) ())


class Category k => HasBinaryProducts k where
  type BinaryProduct k (x :: Kind k) (y :: Kind k) :: Kind k

  proj1 :: Obj k x -> Obj k y -> k (BinaryProduct k x y) x
  proj2 :: Obj k x -> Obj k y -> k (BinaryProduct k x y) y

  (&&&) :: k a x -> k a y -> k a (BinaryProduct k x y)

  (***) :: k a1 b1 -> k a2 b2 -> k (BinaryProduct k a1 a2) (BinaryProduct k b1 b2)
  l *** r = (l . proj1 (src l) (src r)) &&& (r . proj2 (src l) (src r))


type instance LimitFam (i :++: j) k f = BinaryProduct k
  (LimitFam i k (f :.: Inj1 i j))
  (LimitFam j k (f :.: Inj2 i j))

-- | If `k` has binary products, we can take the limit of 2 joined diagrams.
instance (HasLimits i k, HasLimits j k, HasBinaryProducts k) => HasLimits (i :++: j) k where

  limit = limit'
    where
      limit' :: forall f. Obj (Nat (i :++: j) k) f -> Cone f (Limit f)
      limit' l@Nat{} = Nat (Const (x *** y)) (srcF l) h
        where
          x = coneVertex lim1
          y = coneVertex lim2
          lim1 = limit (l `o` natId Inj1)
          lim2 = limit (l `o` natId Inj2)
          h :: Obj (i :++: j) z -> Component (ConstF f (LimitFam (i :++: j) k f)) f z
          h (I1 n) = lim1 ! n . proj1 x y
          h (I2 n) = lim2 ! n . proj2 x y

  limitFactorizer l@Nat{} c =
    limitFactorizer (l `o` natId Inj1) (constPostcompIn (c `o` natId Inj1))
    &&&
    limitFactorizer (l `o` natId Inj2) (constPostcompIn (c `o` natId Inj2))


-- | The tuple is the binary product in @Hask@.
instance HasBinaryProducts (->) where
  type BinaryProduct (->) x y = (x, y)

  proj1 _ _ = \(x, _) -> x
  proj2 _ _ = \(_, y) -> y

  f &&& g = \x -> (f x, g x)
  f *** g = \(x, y) -> (f x, g y)

-- | The product of categories ':**:' is the binary product in 'Cat'.
instance HasBinaryProducts Cat where
  type BinaryProduct Cat c1 c2 = c1 :**: c2

  proj1 (CatA _) (CatA _) = CatA Proj1
  proj2 (CatA _) (CatA _) = CatA Proj2

  CatA f1 &&& CatA f2 = CatA ((f1 :***: f2) :.: DiagProd)
  CatA f1 *** CatA f2 = CatA (f1 :***: f2)

-- | In the category of one object that object is its own product.
instance HasBinaryProducts Unit where
  type BinaryProduct Unit () () = ()

  proj1 Unit Unit = Unit
  proj2 Unit Unit = Unit

  Unit &&& Unit = Unit
  Unit *** Unit = Unit

-- | The binary product of the product of 2 categories is the product of their binary products.
instance (HasBinaryProducts c1, HasBinaryProducts c2) => HasBinaryProducts (c1 :**: c2) where
  type BinaryProduct (c1 :**: c2) (x1, x2) (y1, y2) = (BinaryProduct c1 x1 y1, BinaryProduct c2 x2 y2)

  proj1 (x1 :**: x2) (y1 :**: y2) = proj1 x1 y1 :**: proj1 x2 y2
  proj2 (x1 :**: x2) (y1 :**: y2) = proj2 x1 y1 :**: proj2 x2 y2

  (f1 :**: f2) &&& (g1 :**: g2) = (f1 &&& g1) :**: (f2 &&& g2)
  (f1 :**: f2) *** (g1 :**: g2) = (f1 *** g1) :**: (f2 *** g2)

instance (HasBinaryProducts c1, HasBinaryProducts c2) => HasBinaryProducts (c1 :>>: c2) where
  type BinaryProduct (c1 :>>: c2) (I1 a) (I1 b) = I1 (BinaryProduct c1 a b)
  type BinaryProduct (c1 :>>: c2) (I1 a) (I2 b) = I1 a
  type BinaryProduct (c1 :>>: c2) (I2 a) (I1 b) = I1 b
  type BinaryProduct (c1 :>>: c2) (I2 a) (I2 b) = I2 (BinaryProduct c2 a b)

  proj1 (DC (I1A a)) (DC (I1A b)) = DC (I1A (proj1 a b))
  proj1 (DC (I1A a)) (DC (I2A _)) = DC (I1A a)
  proj1 (DC (I2A a)) (DC (I1A b)) = DC (I12 b a (Const (\() -> ())) ())
  proj1 (DC (I2A a)) (DC (I2A b)) = DC (I2A (proj1 a b))

  proj2 (DC (I1A a)) (DC (I1A b)) = DC (I1A (proj2 a b))
  proj2 (DC (I1A a)) (DC (I2A b)) = DC (I12 a b (Const (\() -> ())) ())
  proj2 (DC (I2A _)) (DC (I1A b)) = DC (I1A b)
  proj2 (DC (I2A a)) (DC (I2A b)) = DC (I2A (proj2 a b))

  DC (I1A a) &&& DC (I1A b) = DC (I1A (a &&& b))
  DC (I1A a) &&& DC (I12 _ _ _ _) = DC (I1A a)
  DC (I12 _ _ _ _) &&& DC (I1A b) = DC (I1A b)
  DC (I2A a) &&& DC (I2A b) = DC (I2A (a &&& b))
  DC (I12 a b1 _ _) &&& DC (I12 _ b2 _ _) = DC (I12 a (b1 *** b2) (Const (\() -> ())) ())


data ProductFunctor (k :: * -> * -> *) = ProductFunctor
-- | Binary product as a bifunctor.
instance HasBinaryProducts k => Functor (ProductFunctor k) where
  type Dom (ProductFunctor k) = k :**: k
  type Cod (ProductFunctor k) = k
  type ProductFunctor k :% (a, b) = BinaryProduct k a b

  ProductFunctor % (a1 :**: a2) = a1 *** a2

-- | A specialisation of the limit adjunction to products.
prodAdj :: HasBinaryProducts k => Adjunction (k :**: k) k (DiagProd k) (ProductFunctor k)
prodAdj = mkAdjunctionUnits DiagProd ProductFunctor (\x -> x &&& x) (\(l :**: r) -> proj1 l r :**: proj2 l r)

data p :*: q where
  (:*:) :: (Functor p, Functor q, Dom p ~ Dom q, Cod p ~ k, Cod q ~ k, HasBinaryProducts k) => p -> q -> p :*: q
-- | The product of two functors, passing the same object to both functors and taking the product of the results.
instance (Category (Dom p), Category (Cod p)) => Functor (p :*: q) where
  type Dom (p :*: q) = Dom p
  type Cod (p :*: q) = Cod p
  type (p :*: q) :% a = BinaryProduct (Cod p) (p :% a) (q :% a)

  (p :*: q) % f = (p % f) *** (q % f)

-- | The functor product ':*:' is the binary product in functor categories.
instance (Category c, HasBinaryProducts d) => HasBinaryProducts (Nat c d) where
  type BinaryProduct (Nat c d) x y = x :*: y

  proj1 (Nat f _ _) (Nat g _ _) = Nat (f :*: g) f (\z -> proj1 (f % z) (g % z))
  proj2 (Nat f _ _) (Nat g _ _) = Nat (f :*: g) g (\z -> proj2 (f % z) (g % z))

  Nat a f af &&& Nat _ g ag = Nat a (f :*: g) (\z -> af z &&& ag z)
  Nat f1 f2 f *** Nat g1 g2 g = Nat (f1 :*: g1) (f2 :*: g2) (\z -> f z *** g z)



class Category k => HasBinaryCoproducts k where
  type BinaryCoproduct k (x :: Kind k) (y :: Kind k) :: Kind k

  inj1 :: Obj k x -> Obj k y -> k x (BinaryCoproduct k x y)
  inj2 :: Obj k x -> Obj k y -> k y (BinaryCoproduct k x y)

  (|||) :: k x a -> k y a -> k (BinaryCoproduct k x y) a

  (+++) :: k a1 b1 -> k a2 b2 -> k (BinaryCoproduct k a1 a2) (BinaryCoproduct k b1 b2)
  l +++ r = (inj1 (tgt l) (tgt r) . l) ||| (inj2 (tgt l) (tgt r) . r)


type instance ColimitFam (i :++: j) k f = BinaryCoproduct k
  (ColimitFam i k (f :.: Inj1 i j))
  (ColimitFam j k (f :.: Inj2 i j))

-- | If `k` has binary coproducts, we can take the colimit of 2 joined diagrams.
instance (HasColimits i k, HasColimits j k, HasBinaryCoproducts k) => HasColimits (i :++: j) k where

  colimit = colimit'
    where
      colimit' :: forall f. Obj (Nat (i :++: j) k) f -> Cocone f (Colimit f)
      colimit' l@Nat{} = Nat (srcF l) (Const (x +++ y)) h
        where
          x = coconeVertex col1
          y = coconeVertex col2
          col1 = colimit (l `o` natId Inj1)
          col2 = colimit (l `o` natId Inj2)
          h :: Obj (i :++: j) z -> Component f (ConstF f (ColimitFam (i :++: j) k f)) z
          h (I1 n) = inj1 x y . col1 ! n
          h (I2 n) = inj2 x y . col2 ! n

  colimitFactorizer l@Nat{} c =
    colimitFactorizer (l `o` natId Inj1) (constPostcompOut (c `o` natId Inj1))
    |||
    colimitFactorizer (l `o` natId Inj2) (constPostcompOut (c `o` natId Inj2))


-- | The coproduct of categories ':++:' is the binary coproduct in 'Cat'.
instance HasBinaryCoproducts Cat where
  type BinaryCoproduct Cat c1 c2 = c1 :++: c2

  inj1 (CatA _) (CatA _) = CatA Inj1
  inj2 (CatA _) (CatA _) = CatA Inj2

  CatA f1 ||| CatA f2 = CatA (CodiagCoprod :.: (f1 :+++: f2))
  CatA f1 +++ CatA f2 = CatA (f1 :+++: f2)

-- | In the category of one object that object is its own coproduct.
instance HasBinaryCoproducts Unit where
  type BinaryCoproduct Unit () () = ()

  inj1 Unit Unit = Unit
  inj2 Unit Unit = Unit

  Unit ||| Unit = Unit
  Unit +++ Unit = Unit

-- | The binary coproduct of the product of 2 categories is the product of their binary coproducts.
instance (HasBinaryCoproducts c1, HasBinaryCoproducts c2) => HasBinaryCoproducts (c1 :**: c2) where
  type BinaryCoproduct (c1 :**: c2) (x1, x2) (y1, y2) = (BinaryCoproduct c1 x1 y1, BinaryCoproduct c2 x2 y2)

  inj1 (x1 :**: x2) (y1 :**: y2) = inj1 x1 y1 :**: inj1 x2 y2
  inj2 (x1 :**: x2) (y1 :**: y2) = inj2 x1 y1 :**: inj2 x2 y2

  (f1 :**: f2) ||| (g1 :**: g2) = (f1 ||| g1) :**: (f2 ||| g2)
  (f1 :**: f2) +++ (g1 :**: g2) = (f1 +++ g1) :**: (f2 +++ g2)

instance (HasBinaryCoproducts c1, HasBinaryCoproducts c2) => HasBinaryCoproducts (c1 :>>: c2) where
  type BinaryCoproduct (c1 :>>: c2) (I1 a) (I1 b) = I1 (BinaryCoproduct c1 a b)
  type BinaryCoproduct (c1 :>>: c2) (I1 a) (I2 b) = I2 b
  type BinaryCoproduct (c1 :>>: c2) (I2 a) (I1 b) = I2 a
  type BinaryCoproduct (c1 :>>: c2) (I2 a) (I2 b) = I2 (BinaryCoproduct c2 a b)

  inj1 (DC (I1A a)) (DC (I1A b)) = DC (I1A (inj1 a b))
  inj1 (DC (I1A a)) (DC (I2A b)) = DC (I12 a b (Const (\() -> ())) ())
  inj1 (DC (I2A a)) (DC (I1A _)) = DC (I2A a)
  inj1 (DC (I2A a)) (DC (I2A b)) = DC (I2A (inj1 a b))

  inj2 (DC (I1A a)) (DC (I1A b)) = DC (I1A (inj2 a b))
  inj2 (DC (I1A _)) (DC (I2A b)) = DC (I2A b)
  inj2 (DC (I2A a)) (DC (I1A b)) = DC (I12 b a (Const (\() -> ())) ())
  inj2 (DC (I2A a)) (DC (I2A b)) = DC (I2A (inj2 a b))

  DC (I1A a) ||| DC (I1A b) = DC (I1A (a ||| b))
  DC (I2A a) ||| DC (I12 _ _ _ _) = DC (I2A a)
  DC (I12 _ _ _ _) ||| DC (I2A b) = DC (I2A b)
  DC (I2A a) ||| DC (I2A b) = DC (I2A (a ||| b))
  DC (I12 a1 b _ _) ||| DC (I12 a2 _ _ _) = DC (I12 (a1 +++ a2) b (Const (\() -> ())) ())


data CoproductFunctor (k :: * -> * -> *) = CoproductFunctor
-- | Binary coproduct as a bifunctor.
instance HasBinaryCoproducts k => Functor (CoproductFunctor k) where
  type Dom (CoproductFunctor k) = k :**: k
  type Cod (CoproductFunctor k) = k
  type CoproductFunctor k :% (a, b) = BinaryCoproduct k a b

  CoproductFunctor % (a1 :**: a2) = a1 +++ a2

-- | A specialisation of the colimit adjunction to coproducts.
coprodAdj :: HasBinaryCoproducts k => Adjunction k (k :**: k) (CoproductFunctor k) (DiagProd k)
coprodAdj = mkAdjunctionUnits CoproductFunctor DiagProd (\(l :**: r) -> inj1 l r :**: inj2 l r) (\x -> x ||| x)

data p :+: q where
  (:+:) :: (Functor p, Functor q, Dom p ~ Dom q, Cod p ~ k, Cod q ~ k, HasBinaryCoproducts k) => p -> q -> p :+: q
-- | The coproduct of two functors, passing the same object to both functors and taking the coproduct of the results.
instance (Category (Dom p), Category (Cod p)) => Functor (p :+: q) where
  type Dom (p :+: q) = Dom p
  type Cod (p :+: q) = Cod p
  type (p :+: q) :% a = BinaryCoproduct (Cod p) (p :% a) (q :% a)

  (p :+: q) % f = (p % f) +++ (q % f)

-- | The functor coproduct ':+:' is the binary coproduct in functor categories.
instance (Category c, HasBinaryCoproducts d) => HasBinaryCoproducts (Nat c d) where
  type BinaryCoproduct (Nat c d) x y = x :+: y

  inj1 (Nat f _ _) (Nat g _ _) = Nat f (f :+: g) (\z -> inj1 (f % z) (g % z))
  inj2 (Nat f _ _) (Nat g _ _) = Nat g (f :+: g) (\z -> inj2 (f % z) (g % z))

  Nat f a fa ||| Nat g _ ga = Nat (f :+: g) a (\z -> fa z ||| ga z)
  Nat f1 f2 f +++ Nat g1 g2 g = Nat (f1 :+: g1) (f2 :+: g2) (\z -> f z +++ g z)

-- | Terminal objects are the dual of initial objects.
instance HasInitialObject k => HasTerminalObject (Op k) where
  type TerminalObject (Op k) = InitialObject k
  terminalObject = Op initialObject
  terminate (Op f) = Op (initialize f)

-- | Terminal objects are the dual of initial objects.
instance HasTerminalObject k => HasInitialObject (Op k) where
  type InitialObject (Op k) = TerminalObject k
  initialObject = Op terminalObject
  initialize (Op f) = Op (terminate f)

-- | Binary products are the dual of binary coproducts.
instance HasBinaryCoproducts k => HasBinaryProducts (Op k) where
  type BinaryProduct (Op k) x y = BinaryCoproduct k x y

  proj1 (Op x) (Op y) = Op (inj1 x y)
  proj2 (Op x) (Op y) = Op (inj2 x y)
  Op f &&& Op g = Op (f ||| g)
  Op f *** Op g = Op (f +++ g)

-- | Binary products are the dual of binary coproducts.
instance HasBinaryProducts k => HasBinaryCoproducts (Op k) where
  type BinaryCoproduct (Op k) x y = BinaryProduct k x y

  inj1 (Op x) (Op y) = Op (proj1 x y)
  inj2 (Op x) (Op y) = Op (proj2 x y)
  Op f ||| Op g = Op (f &&& g)
  Op f +++ Op g = Op (f *** g)




type instance LimitFam Unit k f = f :% ()

-- | The limit of a single object is that object.
instance Category k => HasLimits Unit k where

  limit (Nat f _ _) = Nat (Const (f % Unit)) f (\Unit -> f % Unit)
  limitFactorizer Nat{} n = n ! Unit

type instance LimitFam (i :>>: j) k f = f :% InitialObject (i :>>: j)

-- | The limit of any diagram with an initial object, has the limit at the initial object.
instance (HasInitialObject (i :>>: j), Category i, Category j, Category k) => HasLimits (i :>>: j) k where

  limit (Nat f _ _) = Nat (Const (f % initialObject)) f (\z -> f % initialize z)
  limitFactorizer Nat{} n = n ! initialObject


type instance ColimitFam Unit k f = f :% ()

-- | The colimit of a single object is that object.
instance Category k => HasColimits Unit k where

  colimit (Nat f _ _) = Nat f (Const (f % Unit)) (\Unit -> f % Unit)
  colimitFactorizer Nat{} n = n ! Unit

type instance ColimitFam (i :>>: j) k f = f :% TerminalObject (i :>>: j)

-- | The colimit of any diagram with a terminal object, has the limit at the terminal object.
instance (HasTerminalObject (i :>>: j), Category i, Category j, Category k) => HasColimits (i :>>: j) k where

  colimit (Nat f _ _) = Nat f (Const (f % terminalObject)) (\z -> f % terminate z)
  colimitFactorizer Nat{} n = n ! terminalObject


data ForAll f = ForAll (forall a. Obj (->) a -> f :% a)
type instance LimitFam (->) (->) f = ForAll f

instance HasLimits (->) (->) where
  limit (Nat f _ _) = Nat (Const (\x -> x)) f (\a (ForAll g) -> g a)
  limitFactorizer Nat{} n = \z -> ForAll (\a -> (n ! a) z)

data Exists f = forall a. Exists (Obj (->) a) (f :% a)
type instance ColimitFam (->) (->) f = Exists f

instance HasColimits (->) (->) where
  colimit (Nat f _ _) = Nat f (Const (\x -> x)) Exists
  colimitFactorizer Nat{} n = \(Exists a fa) -> (n ! a) fa
