{-# LANGUAGE
    FlexibleInstances
  , GADTs
  , MultiParamTypeClasses
  , RankNTypes
  , TypeOperators
  , TypeFamilies
  , UndecidableInstances
  , NoImplicitPrelude
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.KanExtension
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.KanExtension where

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction
import Data.Category.Limit
import Data.Category.Unit


-- | An instance of @HasRightKan p k@ says there are right Kan extensions for all functors with codomain @k@.
class (Functor p, Category k) => HasRightKan p k where
  -- | The right Kan extension of a functor @p@ for functors @f@ with codomain @k@.
  type RanFam p k (f :: *) :: *
  -- | 'ran' gives the defining natural transformation of the right Kan extension of @f@ along @p@.
  ran           :: p -> Obj (Nat (Dom p) k) f -> Nat (Dom p) k (RanFam p k f :.: p) f
  -- | 'ranFactorizer' shows that this extension is universal.
  ranFactorizer :: Nat (Dom p) k (h :.: p) f -> Nat (Cod p) k h (RanFam p k f)

type Ran p f = RanFam p (Cod f) f

ranF :: HasRightKan p k => p -> Obj (Nat (Dom p) k) f -> Obj (Nat (Cod p) k) (RanFam p k f)
ranF p f = ranF' (ran p f)

ranF' :: Nat (Dom p) k (RanFam p k f :.: p) f -> Obj (Nat (Cod p) k) (RanFam p k f)
ranF' (Nat (r :.: _) _ _) = natId r

data RanFunctor (p :: *) (k :: * -> * -> *) = RanFunctor p
instance HasRightKan p k => Functor (RanFunctor p k) where
  type Dom (RanFunctor p k) = Nat (Dom p) k
  type Cod (RanFunctor p k) = Nat (Cod p) k
  type RanFunctor p k :% f = RanFam p k f

  RanFunctor p % n = ranFactorizer (n . ran p (src n))

-- | The right Kan extension along @p@ is right adjoint to precomposition with @p@.
ranAdj :: forall p k. HasRightKan p k => p -> Adjunction (Nat (Dom p) k) (Nat (Cod p) k) (Precompose p k) (RanFunctor p k)
ranAdj p = mkAdjunctionTerm (Precompose p) (RanFunctor p) (\_ -> ranFactorizer) (ran p)


-- | An instance of @HasLeftKan p k@ says there are left Kan extensions for all functors with codomain @k@.
class (Functor p, Category k) => HasLeftKan p k where
  -- | The left Kan extension of a functor @p@ for functors @f@ with codomain @k@.
  type LanFam (p :: *) (k :: * -> * -> *) (f :: *) :: *
  -- | 'lan' gives the defining natural transformation of the left Kan extension of @f@ along @p@.
  lan           :: p -> Obj (Nat (Dom p) k) f -> Nat (Dom p) k f (LanFam p k f :.: p)
  -- | 'lanFactorizer' shows that this extension is universal.
  lanFactorizer :: Nat (Dom p) k f (h :.: p) -> Nat (Cod p) k (LanFam p k f) h

type Lan p f = LanFam p (Cod f) f

lanF :: HasLeftKan p k => p -> Obj (Nat (Dom p) k) f -> Obj (Nat (Cod p) k) (LanFam p k f)
lanF p f = lanF' (lan p f)

lanF' :: Nat (Dom p) k f (LanFam p k f :.: p) -> Obj (Nat (Cod p) k) (LanFam p k f)
lanF' (Nat _ (r :.: _) _) = natId r

data LanFunctor (p :: *) (k :: * -> * -> *) = LanFunctor p
instance HasLeftKan p k => Functor (LanFunctor p k) where
  type Dom (LanFunctor p k) = Nat (Dom p) k
  type Cod (LanFunctor p k) = Nat (Cod p) k
  type LanFunctor p k :% f = LanFam p k f

  LanFunctor p % n = lanFactorizer (lan p (tgt n) . n)

-- | The left Kan extension along @p@ is left adjoint to precomposition with @p@.
lanAdj :: forall p k. HasLeftKan p k => p -> Adjunction (Nat (Cod p) k) (Nat (Dom p) k) (LanFunctor p k) (Precompose p k)
lanAdj p = mkAdjunctionInit (LanFunctor p) (Precompose p) (lan p) (\_ -> lanFactorizer)


-- | The right Kan extension of @f@ along a functor to the unit category is the limit of @f@.
instance HasLimits j k => HasRightKan (Const j Unit ()) k where
  type RanFam (Const j Unit ()) k f = Const Unit k (LimitFam j k f)
  ran p f@Nat{} = let cone = limit f in Nat (Const (coneVertex cone) :.: p) (srcF f) (cone !)
  ranFactorizer n@(Nat (h :.: _) _ _) = let fact = limitFactorizer (constPrecompIn n) in Nat h (Const (tgt fact)) (\Unit -> fact)

-- | The left Kan extension of @f@ along a functor to the unit category is the colimit of @f@.
instance HasColimits j k => HasLeftKan (Const j Unit ()) k where
  type LanFam (Const j Unit ()) k f = Const Unit k (ColimitFam j k f)
  lan p f@Nat{} = let cocone = colimit f in Nat (srcF f) (Const (coconeVertex cocone) :.: p) (cocone !)
  lanFactorizer n@(Nat _ (h :.: _) _) = let fact = colimitFactorizer (constPrecompOut n) in Nat (Const (src fact)) h (\Unit -> fact)


-- | Ran id = id
instance (Category j, Category k) => HasRightKan (Id j) k where
  type RanFam (Id j) k f = f
  ran Id (Nat f _ _) = idPrecomp f
  ranFactorizer n@(Nat (h :.: Id) _ _) = n . idPrecompInv h

-- | Lan id = id
instance (Category j, Category k) => HasLeftKan (Id j) k where
  type LanFam (Id j) k f = f
  lan Id (Nat f _ _) = idPrecompInv f
  lanFactorizer n@(Nat _ (h :.: Id) _) = idPrecomp h . n


-- | Ran (q . p) = Ran q . Ran p
instance (HasRightKan q k, HasRightKan p k) => HasRightKan (q :.: p) k where
  type RanFam (q :.: p) k f = RanFam q k (RanFam p k f)
  ran (q :.: p) f = let ranp = ran p f in case ran q (ranF' ranp) of
      ranq@(Nat (r :.: _) _ _) -> ranp . (ranq `o` natId p) . compAssocInv r q p
  ranFactorizer n@(Nat (h :.: (q :.: p)) _ _) = ranFactorizer (ranFactorizer (n . compAssoc h q p))

-- | Lan (q . p) = Lan q . Lan p
instance (HasLeftKan q k, HasLeftKan p k) => HasLeftKan (q :.: p) k where
  type LanFam (q :.: p) k f = LanFam q k (LanFam p k f)
  lan (q :.: p) f = let lanp = lan p f in case lan q (lanF' lanp) of
      lanq@(Nat _ (l :.: _) _) -> compAssoc l q p . (lanq `o` natId p) . lanp
  lanFactorizer n@(Nat _ (h :.: (q :.: p)) _) = lanFactorizer (lanFactorizer (compAssocInv h q p . n))


newtype RanHask p f a = RanHask (forall c. Obj (Dom p) c -> Cod p a (p :% c) -> f :% c)
data RanHaskF p f = RanHaskF
instance Functor p => Functor (RanHaskF p f) where
  type Dom (RanHaskF p f) = Cod p
  type Cod (RanHaskF p f) = (->)
  type RanHaskF p f :% a = RanHask p f a
  RanHaskF % ab = \(RanHask r) -> RanHask (\c bpc -> r c (bpc . ab))

instance Functor p => HasRightKan (Any p) (->) where
  type RanFam (Any p) (->) f = RanHaskF p f
  ran (Any p) (Nat f _ _) = Nat (RanHaskF :.: Any p) f (\z (RanHask r) -> r z (p % z))
  ranFactorizer (Nat (h :.: _) _ n) = Nat h RanHaskF (\_ hz -> RanHask (\c zpc -> n c ((h % zpc) hz)))

data LanHask p f a where
  LanHask :: Obj (Dom p) c -> Cod p (p :% c) a -> f :% c -> LanHask p f a
data LanHaskF p f = LanHaskF
instance Functor p => Functor (LanHaskF p f) where
  type Dom (LanHaskF p f) = Cod p
  type Cod (LanHaskF p f) = (->)
  type LanHaskF p f :% a = LanHask p f a
  LanHaskF % ab = \(LanHask c pca fc) -> LanHask c (ab . pca) fc

instance Functor p => HasLeftKan (Any p) (->) where
  type LanFam (Any p) (->) f = LanHaskF p f
  lan (Any p) (Nat f _ _) = Nat f (LanHaskF :.: Any p) (\z fz -> LanHask z (p % z) fz)
  lanFactorizer (Nat _ (h :.: _) n) = Nat LanHaskF h (\_ (LanHask c pcz fc) -> (h % pcz) (n c fc))
