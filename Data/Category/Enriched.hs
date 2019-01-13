{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , RankNTypes
  , FlexibleContexts
  , NoImplicitPrelude
  , UndecidableInstances
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


type Arr k a b = V k (TerminalObject (V k)) (k $ (a, b))

newtype EOp k a b = EOp (k b a)
instance (ECategory k) => ECategory (EOp k) where
  type V (EOp k) = V k
  type EOp k $ (a, b) = k $ (b, a)
  hom (EOp a) (EOp b) = hom b a
  id (EOp a) = id a
  comp (EOp a) (EOp b) (EOp c) = comp c b a . (proj2 (hom c b) (hom b a) &&& proj1 (hom c b) (hom b a))

newtype Self k a b = Self (k a b)
-- | Self enrichment
instance CartesianClosed k => ECategory (Self k) where
  type V (Self k) = k
  type Self k $ (a, b) = Exponential k a b
  hom (Self a) (Self b) = ExpFunctor % (Op a :**: b)
  id (Self a) = curry terminalObject a a (proj2 terminalObject a)
  comp (Self a) (Self b) (Self c) = curry (bc *** ab) a c (apply b c . (proj1 bc ab *** apply a b) . shuffle)
    where
      bc = c ^^^ b
      ab = b ^^^ a
      shuffle = proj1 (bc *** ab) a &&& (proj2 bc ab *** a)

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

  -- | @:%%@ maps objects.
  type ftag :%% a :: *

  -- | @%%@ maps arrows.
  (%%) :: (EDom ftag ~ k) => ftag -> Obj k a -> Obj k b -> V k (k $ (a, b)) (ECod ftag $ (ftag :%% a, ftag :%% b))

-- | Enriched natural transformations.
data ENat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  ENat :: (EFunctor f, EFunctor g, c ~ EDom f, c ~ EDom g, d ~ ECod f, d ~ ECod g)
    => f -> g -> (forall z. Obj c z -> Arr d (f :%% z) (g :%% z)) -> ENat c d f g

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