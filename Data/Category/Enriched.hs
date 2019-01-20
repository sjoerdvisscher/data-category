{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , RankNTypes
  , FlexibleContexts
  , NoImplicitPrelude
  , UndecidableInstances
  , ScopedTypeVariables
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Enriched
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Enriched where

import Data.Category (Category(..), Obj, Op(..))
import Data.Category.Product
import Data.Category.Functor (Functor(..), Hom(..))
import Data.Category.NaturalTransformation (Nat(..), (!))
import Data.Category.Limit
import Data.Category.CartesianClosed
import Data.Category.Boolean


-- | An enriched category
class CartesianClosed (V k) => ECategory (k :: * -> * -> *) where
  -- | The tensor product of the category V which k is enriched in
  type V k :: * -> * -> *

  -- | The hom object in V from a to b
  type k $ ab :: *
  hom :: Obj k a -> Obj k b -> Obj (V k) (k $ (a, b))

  id :: Obj k a -> Arr k a a
  comp :: Obj k a -> Obj k b -> Obj k c -> V k (BinaryProduct (V k) (k $ (b, c)) (k $ (a, b))) (k $ (a, c))


type Elem k a = V k (TerminalObject (V k)) a

type Arr k a b = Elem k (k $ (a, b))
compArr :: ECategory k => Obj k a -> Obj k b -> Obj k c -> Arr k b c -> Arr k a b -> Arr k a c
compArr a b c f g = comp a b c . (f &&& g)


newtype EOp k a b = EOp (k b a)
instance ECategory k => ECategory (EOp k) where
  type V (EOp k) = V k
  type EOp k $ (a, b) = k $ (b, a)
  hom (EOp a) (EOp b) = hom b a
  id (EOp a) = id a
  comp (EOp a) (EOp b) (EOp c) = comp c b a . (proj2 (hom c b) (hom b a) &&& proj1 (hom c b) (hom b a))

newtype Self v a b = Self (v a b)
-- | Self enrichment
instance CartesianClosed v => ECategory (Self v) where
  type V (Self v) = v
  type Self v $ (a, b) = Exponential v a b
  hom (Self a) (Self b) = ExpFunctor % (Op a :**: b)
  id (Self a) = toSelf a
  comp (Self a) (Self b) (Self c) = curry (bc *** ab) a c (apply b c . (proj1 bc ab *** apply a b) . shuffle)
    where
      bc = c ^^^ b
      ab = b ^^^ a
      shuffle = proj1 (bc *** ab) a &&& (proj2 bc ab *** a)

toSelf :: CartesianClosed v => v a b -> Arr (Self v) a b
toSelf v = curry terminalObject (src v) (tgt v) (v . proj2 terminalObject (src v))

fromSelf :: forall v a b. CartesianClosed v => Obj v a -> Obj v b -> Arr (Self v) a b -> v a b
fromSelf a b arr = uncurry terminalObject a b arr . (terminate a &&& a)


newtype InHask k a b = InHask (k a b)
-- | Any regular category is enriched in (->), aka Hask
instance Category k => ECategory (InHask k) where
  type V (InHask k) = (->)
  type InHask k $ (a, b) = k a b
  hom (InHask a) (InHask b) = Hom % (Op a :**: b)
  id (InHask f) () = f -- meh
  comp _ _ _ (f, g) = f . g


-- | Enriched functors.
class (ECategory (EDom ftag), ECategory (ECod ftag), V (EDom ftag) ~ V (ECod ftag)) => EFunctor ftag where

  -- | The domain, or source category, of the functor.
  type EDom ftag :: * -> * -> *
  -- | The codomain, or target category, of the functor.
  type ECod ftag :: * -> * -> *

  -- | @:%%@ maps objects at the type level
  type ftag :%% a :: *

  -- | @%%@ maps object at the value level
  (%%) :: ftag -> Obj (EDom ftag) a -> Obj (ECod ftag) (ftag :%% a)

  -- | `map` maps arrows.
  map :: (EDom ftag ~ k) => ftag -> Obj k a -> Obj k b -> V k (k $ (a, b)) (ECod ftag $ (ftag :%% a, ftag :%% b))

  
-- | Enriched natural transformations.
data ENat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  ENat :: (EFunctor f, EFunctor g, c ~ EDom f, c ~ EDom g, d ~ ECod f, d ~ ECod g)
    => f -> g -> (forall z. Obj c z -> Arr d (f :%% z) (g :%% z)) -> ENat c d f g



-- | The enriched functor @k(x, -)@
data EHomX_ k x = EHomX_ (Obj k x)
instance ECategory k => EFunctor (EHomX_ k x) where
  type EDom (EHomX_ k x) = k
  type ECod (EHomX_ k x) = Self (V k)
  type EHomX_ k x :%% y = k $ (x, y)
  EHomX_ x %% y = Self (hom x y)
  map (EHomX_ x) a b = curry (hom a b) (hom x a) (hom x b) (comp x a b)

-- | The enriched functor @k(-, x)@
data EHom_X k x = EHom_X (Obj (EOp k) x)
instance ECategory k => EFunctor (EHom_X k x) where
  type EDom (EHom_X k x) = EOp k
  type ECod (EHom_X k x) = Self (V k)
  type EHom_X k x :%% y = k $ (y, x)
  EHom_X x %% y = Self (hom x y)
  map (EHom_X x) a b = curry (hom a b) (hom x a) (hom x b) (comp x a b)



yoneda :: forall f k x. (EFunctor f, EDom f ~ k, ECod f ~ Self (V k)) => Obj k x -> ENat k (Self (V k)) (EHomX_ k x) f -> Elem k (f :%% x)
yoneda x (ENat _ f n) = nx . id x
  where 
    fx :: Obj (V k) (f :%% x)
    Self fx = f %% x
    nx :: V k (k $ (x, x)) (f :%% x)
    nx = fromSelf (hom x x) fx (n x)

yonedaInv :: forall f k x. (EFunctor f, EDom f ~ k, ECod f ~ Self (V k)) => f -> Obj k x -> Elem k (f :%% x) -> ENat k (Self (V k)) (EHomX_ k x) f
yonedaInv f x fx = ENat (EHomX_ x) f (\a -> toSelf (c a))
  where
    c :: forall a. Obj k a -> V k (k $ (x, a)) (f :%% a)
    c a = apply (tgt fx) fa . (map f x a *** fx) . (hom x a &&& terminate (hom x a))
      where
        Self fa = f %% a



data One
data Two
data Three
data PosetTest a b where
  One :: PosetTest One One
  Two :: PosetTest Two Two
  Three :: PosetTest Three Three

type family Poset3 a b where
  Poset3 Two One = Fls
  Poset3 Three One = Fls
  Poset3 Three Two = Fls
  Poset3 a b = Tru
instance ECategory PosetTest where
  type V PosetTest = Boolean
  type PosetTest $ (a, b) = Poset3 a b
  hom One One = Tru
  hom One Two = Tru
  hom One Three = Tru
  hom Two One = Fls
  hom Two Two = Tru
  hom Two Three = Tru
  hom Three One = Fls
  hom Three Two = Fls
  hom Three Three = Tru

  id One = Tru
  id Two = Tru
  id Three = Tru
  comp One One One = Tru
  comp One One Two = Tru
  comp One One Three = Tru
  comp One Two One = F2T
  comp One Two Two = Tru
  comp One Two Three = Tru
  comp One Three One = F2T
  comp One Three Two = F2T
  comp One Three Three = Tru
  comp Two One One = Fls
  comp Two One Two = F2T
  comp Two One Three = F2T
  comp Two Two One = Fls
  comp Two Two Two = Tru
  comp Two Two Three = Tru
  comp Two Three One = Fls
  comp Two Three Two = F2T
  comp Two Three Three = Tru
  comp Three One One = Fls
  comp Three One Two = Fls
  comp Three One Three = F2T
  comp Three Two One = Fls
  comp Three Two Two = Fls
  comp Three Two Three = F2T
  comp Three Three One = Fls
  comp Three Three Two = Fls
  comp Three Three Three = Tru