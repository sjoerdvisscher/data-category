{-# LANGUAGE
    TypeOperators
  , TypeFamilies
  , GADTs
  , Rank2Types
  , ViewPatterns
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , NoImplicitPrelude
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Monoidal
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Monoidal where

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction
import Data.Category.Limit
import Data.Category.Product


-- | A monoidal category is a category with some kind of tensor product.
--   A tensor product is a bifunctor, with a unit object.
class (Functor f, Dom f ~ (Cod f :**: Cod f)) => TensorProduct f where

  type Unit f :: *
  unitObject :: f -> Obj (Cod f) (Unit f)

  leftUnitor     :: Cod f ~ k => f -> Obj k a -> k (f :% (Unit f, a)) a
  leftUnitorInv  :: Cod f ~ k => f -> Obj k a -> k a (f :% (Unit f, a))
  rightUnitor    :: Cod f ~ k => f -> Obj k a -> k (f :% (a, Unit f)) a
  rightUnitorInv :: Cod f ~ k => f -> Obj k a -> k a (f :% (a, Unit f))

  associator     :: Cod f ~ k => f -> Obj k a -> Obj k b -> Obj k c -> k (f :% (f :% (a, b), c)) (f :% (a, f :% (b, c)))
  associatorInv  :: Cod f ~ k => f -> Obj k a -> Obj k b -> Obj k c -> k (f :% (a, f :% (b, c))) (f :% (f :% (a, b), c))

class TensorProduct f => SymmetricTensorProduct f where
  swap :: Cod f ~ k => f -> Obj k a -> Obj k b -> k (f :% (a, b)) (f :% (b, a))

-- | If a category has all products, then the product functor makes it a monoidal category,
--   with the terminal object as unit.
instance (HasTerminalObject k, HasBinaryProducts k) => TensorProduct (ProductFunctor k) where

  type Unit (ProductFunctor k) = TerminalObject k
  unitObject _ = terminalObject

  leftUnitor     _ a = proj2 terminalObject a
  leftUnitorInv  _ a = terminate a &&& a
  rightUnitor    _ a = proj1 a terminalObject
  rightUnitorInv _ a = a &&& terminate a

  associator    _ a b c = (proj1 a b . proj1 (a *** b) c) &&& (proj2 a b *** c)
  associatorInv _ a b c = (a *** proj1 b c) &&& (proj2 b c . proj2 a (b *** c))

instance (HasTerminalObject k, HasBinaryProducts k) => SymmetricTensorProduct (ProductFunctor k) where
  swap _ a b = proj2 a b &&& proj1 a b

-- | If a category has all coproducts, then the coproduct functor makes it a monoidal category,
--   with the initial object as unit.
instance (HasInitialObject k, HasBinaryCoproducts k) => TensorProduct (CoproductFunctor k) where

  type Unit (CoproductFunctor k) = InitialObject k
  unitObject _ = initialObject

  leftUnitor     _ a = initialize a ||| a
  leftUnitorInv  _ a = inj2 initialObject a
  rightUnitor    _ a = a ||| initialize a
  rightUnitorInv _ a = inj1 a initialObject

  associator    _ a b c = (a +++ inj1 b c) ||| (inj2 a (b +++ c) . inj2 b c)
  associatorInv _ a b c = (inj1 (a +++ b) c . inj1 a b) ||| (inj2 a b +++ c)

instance (HasInitialObject k, HasBinaryCoproducts k) => SymmetricTensorProduct (CoproductFunctor k) where
  swap _ a b = inj2 b a ||| inj1 b a

-- | Functor composition makes the category of endofunctors monoidal, with the identity functor as unit.
instance Category k => TensorProduct (EndoFunctorCompose k) where

  type Unit (EndoFunctorCompose k) = Id k
  unitObject _ = natId Id

  leftUnitor     _ (Nat g _ _) = idPostcomp g
  leftUnitorInv  _ (Nat g _ _) = idPostcompInv g
  rightUnitor    _ (Nat g _ _) = idPrecomp g
  rightUnitorInv _ (Nat g _ _) = idPrecompInv g

  associator    _ (Nat f _ _) (Nat g _ _) (Nat h _ _) = compAssoc f g h
  associatorInv _ (Nat f _ _) (Nat g _ _) (Nat h _ _) = compAssocInv f g h


-- | @MonoidObject f a@ defines a monoid @a@ in a monoidal category with tensor product @f@.
data MonoidObject f a = MonoidObject
  { unit     :: Cod f (Unit f)        a
  , multiply :: Cod f ((f :% (a, a))) a
  }

trivialMonoid :: TensorProduct f => f -> MonoidObject f (Unit f)
trivialMonoid f = MonoidObject (unitObject f) (leftUnitor f (unitObject f))

coproductMonoid :: (HasInitialObject k, HasBinaryCoproducts k) => Obj k a -> MonoidObject (CoproductFunctor k) a
coproductMonoid a = MonoidObject (initialize a) (a ||| a)


-- | @ComonoidObject f a@ defines a comonoid @a@ in a comonoidal category with tensor product @f@.
data ComonoidObject f a = ComonoidObject
  { counit     :: Cod f a (Unit f)
  , comultiply :: Cod f a (f :% (a, a))
  }

trivialComonoid :: TensorProduct f => f -> ComonoidObject f (Unit f)
trivialComonoid f = ComonoidObject (unitObject f) (leftUnitorInv f (unitObject f))

productComonoid :: (HasTerminalObject k, HasBinaryProducts k) => Obj k a -> ComonoidObject (ProductFunctor k) a
productComonoid a = ComonoidObject (terminate a) (a &&& a)


data MonoidAsCategory f m a b where
  MonoidValue :: (TensorProduct f, Dom f ~ (k :**: k), Cod f ~ k)
              => f -> MonoidObject f m -> k (Unit f) m -> MonoidAsCategory f m m m

-- | A monoid as a category with one object.
instance Category (MonoidAsCategory f m) where

  src (MonoidValue f m _) = MonoidValue f m (unit m)
  tgt (MonoidValue f m _) = MonoidValue f m (unit m)

  MonoidValue f m a . MonoidValue _ _ b = MonoidValue f m (multiply m . f % (a :**: b) . leftUnitorInv f (unitObject f))


-- | A monad is a monoid in the category of endofunctors.
type Monad f = MonoidObject (EndoFunctorCompose (Dom f)) f

mkMonad :: (Functor f, Dom f ~ k, Cod f ~ k)
  => f
  -> (forall a. Obj k a -> Component (Id k) f a)
  -> (forall a. Obj k a -> Component (f :.: f) f a)
  -> Monad f
mkMonad f ret join = MonoidObject
  { unit     = Nat Id        f ret
  , multiply = Nat (f :.: f) f join
  }

monadFunctor :: Monad f -> f
monadFunctor (unit -> Nat _ f _) = f

idMonad :: Category k => Monad (Id k)
idMonad = MonoidObject (natId Id) (idPrecomp Id)


-- | A comonad is a comonoid in the category of endofunctors.
type Comonad f = ComonoidObject (EndoFunctorCompose (Dom f)) f

mkComonad :: (Functor f, Dom f ~ k, Cod f ~ k)
  => f
  -> (forall a. Obj k a -> Component f (Id k) a)
  -> (forall a. Obj k a -> Component f (f :.: f) a)
  -> Comonad f
mkComonad f extr dupl = ComonoidObject
  { counit     = Nat f Id        extr
  , comultiply = Nat f (f :.: f) dupl
  }

idComonad :: Category k => Comonad (Id k)
idComonad = ComonoidObject (natId Id) (idPrecompInv Id)


-- | Every adjunction gives rise to an associated monad.
adjunctionMonad :: Adjunction c d f g -> Monad (g :.: f)
adjunctionMonad adj@(Adjunction f g _ _) =
  let MonoidObject ret mult = adjunctionMonadT adj idMonad
  in mkMonad (g :.: f) (ret !) (mult !)

-- | Every adjunction gives rise to an associated monad transformer.
adjunctionMonadT :: (Dom m ~ c) => Adjunction c d f g -> Monad m -> Monad (g :.: m :.: f)
adjunctionMonadT adj@(Adjunction f g _ _) (MonoidObject ret@(Nat _ m _) mult) = mkMonad (g :.: m :.: f)
  ((Wrap g f % ret . idPrecompInv g `o` natId f . adjunctionUnit adj) !)
  ((Wrap g f % (mult . idPrecomp m `o` natId m . Wrap m m % adjunctionCounit adj)) !)

-- | Every adjunction gives rise to an associated comonad.
adjunctionComonad :: Adjunction c d f g -> Comonad (f :.: g)
adjunctionComonad adj@(Adjunction f g _ _) =
  let ComonoidObject extr dupl = adjunctionComonadT adj idComonad
  in mkComonad (f :.: g) (extr !) (dupl !)

-- | Every adjunction gives rise to an associated comonad transformer.
adjunctionComonadT :: (Dom w ~ d) => Adjunction c d f g -> Comonad w -> Comonad (f :.: w :.: g)
adjunctionComonadT adj@(Adjunction f g _ _) (ComonoidObject extr@(Nat w _ _) dupl) = mkComonad (f :.: w :.: g)
  ((adjunctionCounit adj . idPrecomp f `o` natId g . Wrap f g % extr) !)
  ((Wrap f g % (Wrap w w % adjunctionUnit adj . idPrecompInv w `o` natId w . dupl)) !)
