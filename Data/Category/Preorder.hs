{-# LANGUAGE GADTs, TypeFamilies, PatternSynonyms, ScopedTypeVariables, RankNTypes, TypeOperators #-}
module Data.Category.Preorder where

import Prelude hiding ((.), id, Functor)

import Data.Category
import Data.Category.Limit
import Data.Category.CartesianClosed
import Data.Category.Functor
import Data.Category.Adjunction
import Data.Category.Enriched hiding (HasEnds(..))

data Preorder a x y where
  (:<=:) :: a -> a -> Preorder a x y

pattern Obj :: a -> Preorder a x y
pattern Obj a <- a :<=: _ where
  Obj a = a :<=: a
{-# COMPLETE Obj #-} -- Note: only complete for identity arrows `Obj Preorder a`

unObj :: Obj (Preorder a) x -> a
unObj (Obj a) = a

instance Eq a => Category (Preorder a) where
  src (s :<=: _) = Obj s
  tgt (_ :<=: t) = Obj t
  (b :<=: c) . (a :<=: b') = if b == b' then a :<=: c else error "Invalid composition"

instance (Eq a, Bounded a) => HasInitialObject (Preorder a) where
  type InitialObject (Preorder a) = ()
  initialObject = Obj minBound
  initialize (Obj a) = minBound :<=: a

instance (Eq a, Bounded a) => HasTerminalObject (Preorder a) where
  type TerminalObject (Preorder a) = ()
  terminalObject = Obj maxBound
  terminate (Obj a) = a :<=: maxBound

instance Ord a => HasBinaryProducts (Preorder a) where
  type BinaryProduct (Preorder a) x y = ()
  proj1 (Obj a) (Obj b) = min a b :<=: a
  proj2 (Obj a) (Obj b) = min a b :<=: b
  (a :<=: x) &&& (_a :<=: y) = a :<=: min x y

instance Ord a => HasBinaryCoproducts (Preorder a) where
  type BinaryCoproduct (Preorder a) x y = ()
  inj1 (Obj a) (Obj b) = a :<=: max a b
  inj2 (Obj a) (Obj b) = b :<=: max a b
  (x :<=: a) ||| (y :<=: _a) = max x y :<=: a

-- | `ordExp a b` is the largest x such that min x a <= b
ordExp :: (Ord a, Bounded a) => a -> a -> a
ordExp a b = if a <= b then maxBound else b

instance (Ord a, Bounded a) => CartesianClosed (Preorder a) where
  type Exponential (Preorder a) x y = ()
  apply (Obj a) (Obj b) = min (ordExp a b) a :<=: b
  tuple (Obj a) (Obj b) = b :<=: ordExp a (min a b)
  (z1 :<=: z2) ^^^ (y2 :<=: y1) = ordExp y1 z1 :<=: ordExp y2 z2


class Category k => EnumObjs k where
  enumObjs :: (forall a. Obj k a -> r) -> [r]

glb :: (Ord a, Bounded a) => [a] -> a
glb [] = maxBound
glb xs = minimum xs


type End' t = ()
end
  :: (VProfunctor k k t, V k ~ Preorder a, EnumObjs k, Ord a, Bounded a)
  => t -> Obj (Preorder a) (End' t)
end t = Obj $ glb (enumObjs (\a -> unObj (getSelf (t %% (EOp a :<>: a)))))

endCounit
  :: (VProfunctor k k t, V k ~ Preorder a, EnumObjs k, Ord a, Bounded a)
  => t -> Obj k b -> Preorder a (End' t) (t :%% (b, b))
endCounit t a = unObj (end t) :<=: unObj (getSelf (t %% (EOp a :<>: a)))

endFactorizer
  :: (VProfunctor k k t, V k ~ Preorder a, EnumObjs k, Ord a, Bounded a)
  => t -> Obj (Preorder a) x -> (forall b. Obj k b -> Preorder a x (t :%% (b, b))) -> Preorder a x (End' t)
endFactorizer _ (Obj x) f = x :<=: glb (enumObjs (\b -> case f b of _ :<=: tbb -> tbb))


data Floor = Floor
instance Functor Floor where
  type Dom Floor = Preorder Double
  type Cod Floor = Preorder Integer
  type Floor :% a = ()
  Floor % (a :<=: b) = floor a :<=: floor b

data FromInteger = FromInteger
instance Functor FromInteger where
  type Dom FromInteger = Preorder Integer
  type Cod FromInteger = Preorder Double
  type FromInteger :% a = ()
  FromInteger % (a :<=: b) = fromInteger a :<=: fromInteger b

floorGaloisConnection :: Adjunction (Preorder Double) (Preorder Integer) FromInteger Floor
floorGaloisConnection = mkAdjunction FromInteger Floor
  (\(Obj a) (_fromIntegerA :<=: b) -> a :<=: floor b)
  (\(Obj b) (a :<=: _floorB) -> fromInteger a :<=: b)