{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , RankNTypes
  , PatternSynonyms
  , FlexibleContexts
  , NoImplicitPrelude
  , UndecidableInstances
  , ScopedTypeVariables
  , ConstraintKinds
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
import Data.Category.Limit hiding (HasLimits)
import Data.Category.CartesianClosed
import Data.Category.Boolean


-- | An enriched category
class CartesianClosed (V k) => ECategory (k :: * -> * -> *) where
  -- | The category V which k is enriched in
  type V k :: * -> * -> *

  -- | The hom object in V from a to b
  type k $ ab :: *
  hom :: Obj k a -> Obj k b -> Obj (V k) (k $ (a, b))

  id :: Obj k a -> Arr k a a
  comp :: Obj k a -> Obj k b -> Obj k c -> V k (BinaryProduct (V k) (k $ (b, c)) (k $ (a, b))) (k $ (a, c))


-- | Arrows as elements of @k@
type Arr k a b = V k (TerminalObject (V k)) (k $ (a, b))

compArr :: ECategory k => Obj k a -> Obj k b -> Obj k c -> Arr k b c -> Arr k a b -> Arr k a c
compArr a b c f g = comp a b c . (f &&& g)


data Underlying k a b = Underlying (Obj k a) (Arr k a b) (Obj k b)
-- | The underlying category of an enriched category
instance ECategory k => Category (Underlying k) where
  src (Underlying a _ _) = Underlying a (id a) a
  tgt (Underlying _ _ b) = Underlying b (id b) b
  Underlying b f c . Underlying a g _ = Underlying a (compArr a b c f g) c


newtype EOp k a b = EOp (k b a)
-- | The opposite of an enriched category
instance ECategory k => ECategory (EOp k) where
  type V (EOp k) = V k
  type EOp k $ (a, b) = k $ (b, a)
  hom (EOp a) (EOp b) = hom b a
  id (EOp a) = id a
  comp (EOp a) (EOp b) (EOp c) = comp c b a . (proj2 (hom c b) (hom b a) &&& proj1 (hom c b) (hom b a))


data (:<>:) :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  (:<>:) :: (V k1 ~ V k2) => Obj k1 a1 -> Obj k2 a2 -> (:<>:) k1 k2 (a1, a2) (a1, a2)

-- | The enriched product category of enriched categories @c1@ and @c2@.
instance (ECategory k1, ECategory k2, V k1 ~ V k2) => ECategory (k1 :<>: k2) where
  type V (k1 :<>: k2) = V k1
  type (k1 :<>: k2) $ ((a1, a2), (b1, b2)) = BinaryProduct (V k1) (k1 $ (a1, b1)) (k2 $ (a2, b2))
  hom (a1 :<>: a2) (b1 :<>: b2) = hom a1 b1 *** hom a2 b2
  id (a1 :<>: a2) = id a1 &&& id a2
  comp (a1 :<>: a2) (b1 :<>: b2) (c1 :<>: c2) =
    comp a1 b1 c1 . (proj1 bc1 bc2 . proj1 l r &&& proj1 ab1 ab2 . proj2 l r) &&&
    comp a2 b2 c2 . (proj2 bc1 bc2 . proj1 l r &&& proj2 ab1 ab2 . proj2 l r)
    where
      ab1 = hom a1 b1
      ab2 = hom a2 b2
      bc1 = hom b1 c1
      bc2 = hom b2 c2
      l = bc1 *** bc2
      r = ab1 *** ab2


newtype Self v a b = Self { getSelf :: v a b }
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

type EFunctorOf a b t = (EFunctor t, EDom t ~ a, ECod t ~ b)


data Id (k :: * -> * -> *) = Id
-- | The identity functor on k
instance ECategory k => EFunctor (Id k) where
  type EDom (Id k) = k
  type ECod (Id k) = k
  type Id k :%% a = a
  Id %% a = a
  map Id = hom

data (g :.: h) where
  (:.:) :: (EFunctor g, EFunctor h, ECod h ~ EDom g) => g -> h -> g :.: h
-- | The composition of two functors.
instance (ECategory (ECod g), ECategory (EDom h), V (EDom h) ~ V (ECod g), ECod h ~ EDom g) => EFunctor (g :.: h) where
  type EDom (g :.: h) = EDom h
  type ECod (g :.: h) = ECod g
  type (g :.: h) :%% a = g :%% (h :%% a)
  (g :.: h) %% a = g %% (h %% a)
  map (g :.: h) a b = map g (h %% a) (h %% b) . map h a b

data Const (c1 :: * -> * -> *) (c2 :: * -> * -> *) x where
  Const :: Obj c2 x -> Const c1 c2 x
-- | The constant functor.
instance (ECategory c1, ECategory c2, V c1 ~ V c2) => EFunctor (Const c1 c2 x) where
  type EDom (Const c1 c2 x) = c1
  type ECod (Const c1 c2 x) = c2
  type Const c1 c2 x :%% a = x
  Const x %% _ = x
  map (Const x) a b = id x . terminate (hom a b)

data Opposite f where
  Opposite :: EFunctor f => f -> Opposite f
-- | The dual of a functor
instance (EFunctor f) => EFunctor (Opposite f) where
  type EDom (Opposite f) = EOp (EDom f)
  type ECod (Opposite f) = EOp (ECod f)
  type Opposite f :%% a = f :%% a
  Opposite f %% EOp a = EOp (f %% a)
  map (Opposite f) (EOp a) (EOp b) = map f b a

data f1 :<*>: f2 = f1 :<*>: f2
-- | @f1 :<*>: f2@ is the product of the functors @f1@ and @f2@.
instance (EFunctor f1, EFunctor f2, V (ECod f1) ~ V (ECod f2)) => EFunctor (f1 :<*>: f2) where
  type EDom (f1 :<*>: f2) = EDom f1 :<>: EDom f2
  type ECod (f1 :<*>: f2) = ECod f1 :<>: ECod f2
  type (f1 :<*>: f2) :%% (a1, a2) = (f1 :%% a1, f2 :%% a2)
  (f1 :<*>: f2) %% (a1 :<>: a2) = (f1 %% a1) :<>: (f2 %% a2)
  map (f1 :<*>: f2) (a1 :<>: a2) (b1 :<>: b2) = map f1 a1 b1 *** map f2 a2 b2

data DiagProd (k :: * -> * -> *) = DiagProd
-- | 'DiagProd' is the diagonal functor for products.
instance ECategory k => EFunctor (DiagProd k) where
  type EDom (DiagProd k) = k
  type ECod (DiagProd k) = k :<>: k
  type DiagProd k :%% a = (a, a)
  DiagProd %% a = a :<>: a
  map DiagProd a b = hom a b &&& hom a b

newtype UnderlyingF f = UnderlyingF f
-- | The underlying functor of an enriched functor @f@
instance EFunctor f => Functor (UnderlyingF f) where
  type Dom (UnderlyingF f) = Underlying (EDom f)
  type Cod (UnderlyingF f) = Underlying (ECod f)
  type UnderlyingF f :% a = f :%% a
  UnderlyingF f % Underlying a ab b = Underlying (f %% a) (map f a b . ab) (f %% b)


data EHom (k :: * -> * -> *) = EHom
instance ECategory k => EFunctor (EHom k) where
  type EDom (EHom k) = EOp k :<>: k
  type ECod (EHom k) = Self (V k)
  type EHom k :%% (a, b) = k $ (a, b)
  EHom %% (EOp a :<>: b) = Self (hom a b)
  map EHom (EOp a1 :<>: a2) (EOp b1 :<>: b2) = curry (ba *** ab) a b (comp b1 a1 b2 . (comp a1 a2 b2 . (proj2 ba ab *** a) &&& proj1 ba ab . proj1 (ba *** ab) a))
    where
      a = hom a1 a2
      b = hom b1 b2
      ba = hom b1 a1
      ab = hom a2 b2


-- | Enriched natural transformations.
data ENat :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
  ENat :: (EFunctorOf c d f, EFunctorOf c d g)
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



type VProfunctor k l t = EFunctorOf (EOp k :<>: l) (Self (V k)) t

class CartesianClosed v => HasEnds v where
  type End (v :: * -> * -> *) t :: *
  end :: (VProfunctor k k t, V k ~ v) => t -> Obj v (End v t)
  endCounit :: (VProfunctor k k t, V k ~ v) => t -> Obj k a -> v (End v t) (t :%% (a, a))
  endFactorizer :: (VProfunctor k k t, V k ~ v) => t -> (forall a. Obj k a -> v x (t :%% (a, a))) -> v x (End v t)


newtype HaskEnd t = HaskEnd { getHaskEnd :: forall k a. VProfunctor k k t => t -> Obj k a -> t :%% (a, a) }
instance HasEnds (->) where
  type End (->) t = HaskEnd t
  end _ e = e
  endCounit t a (HaskEnd e) = e t a
  endFactorizer _ e x = HaskEnd (\_ a -> e a x)


data FunCat a b t s where
  FArr :: (EFunctorOf a b t, EFunctorOf a b s) => t -> s -> FunCat a b t s

type t :->>: s = EHom (ECod t) :.: (Opposite t :<*>: s)
(->>) :: (EFunctor t, EFunctor s, ECod t ~ ECod s, V (ECod t) ~ V (ECod s)) => t -> s -> t :->>: s
t ->> s = EHom :.: (Opposite t :<*>: s)
-- | The enriched functor category @[a, b]@
instance (HasEnds (V a), V a ~ V b) => ECategory (FunCat a b) where
  type V (FunCat a b) = V a
  type FunCat a b $ (t, s) = End (V a) (t :->>: s)
  hom (FArr t _) (FArr s _) = end (t ->> s)
  id (FArr t _) = endFactorizer (t ->> t) (\a -> id (t %% a))
  comp (FArr t _) (FArr s _) (FArr r _) = endFactorizer (t ->> r)
    (\a -> comp (t %% a) (s %% a) (r %% a) . (endCounit (s ->> r) a *** endCounit (t ->> s) a))


data EndFunctor (k :: * -> * -> *) = EndFunctor
instance (HasEnds (V k), ECategory k) => EFunctor (EndFunctor k) where
  type EDom (EndFunctor k) = FunCat (EOp k :<>: k) (Self (V k))
  type ECod (EndFunctor k) = Self (V k)
  type EndFunctor k :%% t = End (V k) t
  EndFunctor %% (FArr t _) = Self (end t)
  map EndFunctor (FArr f _) (FArr g _) = curry (end (f ->> g)) (end f) (end g) (endFactorizer g (\a ->
    let aa = EOp a :<>: a in apply (getSelf (f %% aa)) (getSelf (g %% aa)) . (endCounit (f ->> g) aa *** endCounit f a)))


-- d :: j -> k, w :: j -> Self (V k)
type family WeigtedLimit (k :: * -> * -> *) w d :: *
type Lim w d = WeigtedLimit (ECod d) w d

class HasEnds (V k) => HasLimits k where
  limitObj :: (EFunctorOf j k d, EFunctorOf j (Self (V k)) w) => w -> d -> Obj k (Lim w d)
  limit    :: (EFunctorOf j k d, EFunctorOf j (Self (V k)) w) => w -> d -> Obj k e -> V k (End (V k) (w :->>: (EHomX_ k e :.: d))) (k $ (e, Lim w d))
  limitInv :: (EFunctorOf j k d, EFunctorOf j (Self (V k)) w) => w -> d -> Obj k e -> V k (k $ (e, Lim w d)) (End (V k) (w :->>: (EHomX_ k e :.: d)))

-- d :: j -> k, w :: EOp j -> Self (V k)
type family WeigtedColimit (k :: * -> * -> *) w d :: *
type Colim w d = WeigtedColimit (ECod d) w d

class HasEnds (V k) => HasColimits k where
  colimitObj :: (EFunctorOf j k d, EFunctorOf (EOp j) (Self (V k)) w) => w -> d -> Obj k (Colim w d)
  colimit    :: (EFunctorOf j k d, EFunctorOf (EOp j) (Self (V k)) w) => w -> d -> Obj k e -> V k (End (V k) (w :->>: (EHom_X k e :.: Opposite d))) (k $ (Colim w d, e))
  colimitInv :: (EFunctorOf j k d, EFunctorOf (EOp j) (Self (V k)) w) => w -> d -> Obj k e -> V k (k $ (Colim w d, e)) (End (V k) (w :->>: (EHom_X k e :.: Opposite d)))


type instance WeigtedLimit (Self v) w d = End v (w :->>: d)
instance HasEnds v => HasLimits (Self v) where
  limitObj w d = Self (end (w ->> d))
  limit w d (Self e) = let wed = w ->> (EHomX_ (Self e) :.: d) in curry (end wed) e (end (w ->> d))
    (endFactorizer (w ->> d) (\a -> let { Self wa = w %% a; Self da = d %% a } in apply e (da ^^^ wa) . (flip wa e da . endCounit wed a *** e)))
  limitInv w d (Self e) = let wed = w ->> (EHomX_ (Self e) :.: d) in endFactorizer wed
    (\a -> let { Self wa = w %% a; Self da = d %% a } in flip e wa da . (endCounit (w ->> d) a ^^^ e))



yoneda    :: forall f k x. (HasEnds (V k), EFunctorOf k (Self (V k)) f) => f -> Obj k x -> V k (End (V k) (EHomX_ k x :->>: f)) (f :%% x)
yoneda f x = apply (hom x x) (getSelf (f %% x)) . (endCounit (EHomX_ x ->> f) x &&& id x . terminate (end (EHomX_ x ->> f)))

yonedaInv :: forall f k x. (HasEnds (V k), EFunctorOf k (Self (V k)) f) => f -> Obj k x -> V k (f :%% x) (End (V k) (EHomX_ k x :->>: f))
yonedaInv f x = endFactorizer (EHomX_ x ->> f) h
  where
    h :: Obj k a -> V k (f :%% x) (Exponential (V k) (k $ (x, a)) (f :%% a))
    h a = curry fx xa fa (apply fx fa . (map f x a . proj2 fx xa &&& proj1 fx xa))
      where
        xa = hom x a
        Self fx = f %% x
        Self fa = f %% a

data Y (k :: * -> * -> *) = Y
-- | Yoneda embedding
instance (ECategory k, HasEnds (V k)) => EFunctor (Y k) where
  type EDom (Y k) = EOp k
  type ECod (Y k) = FunCat k (Self (V k))
  type Y k :%% x = EHomX_ k x
  Y %% EOp x = FArr (EHomX_ x) (EHomX_ x)
  map Y (EOp a) (EOp b) = yonedaInv (EHomX_ b) a


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
