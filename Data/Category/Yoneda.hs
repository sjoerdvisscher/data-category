{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, PatternSynonyms, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Yoneda
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Yoneda where

import Data.Kind (Type)

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction

type YonedaEmbedding k = Curry2 (Op k) k (Hom k)
-- | The Yoneda embedding functor, @C -> Set^(C^op)@.
pattern YonedaEmbedding :: Category k => YonedaEmbedding k
pattern YonedaEmbedding = Curry2 Hom


data Yoneda (k :: Type -> Type -> Type) f = Yoneda
-- | 'Yoneda' converts a functor @f@ into a natural transformation from the hom functor to f.
instance (Category k, Functor f, Dom f ~ Op k, Cod f ~ (->)) => Functor (Yoneda k f) where
  type Dom (Yoneda k f) = Op k
  type Cod (Yoneda k f) = (->)
  type Yoneda k f :% a = Nat (Op k) (->) (k :-*: a) f
  Yoneda % Op ab = \n -> n . YonedaEmbedding % ab


-- | 'fromYoneda' and 'toYoneda' are together the isomophism from the Yoneda lemma.
fromYoneda :: (Category k, Functor f, Dom f ~ Op k, Cod f ~ (->)) => f -> Nat (Op k) (->) (Yoneda k f) f
fromYoneda f = Nat Yoneda f (\(Op a) n -> (n ! Op a) a)

toYoneda   :: (Category k, Functor f, Dom f ~ Op k, Cod f ~ (->)) => f -> Nat (Op k) (->) f (Yoneda k f)
toYoneda   f = Nat f Yoneda (\(Op a) fa -> Nat (Hom_X a) f (\_ h -> (f % Op h) fa))


haskUnit :: Obj (->) ()
haskUnit = obj

data M1 = M1
instance Functor M1 where
  type Dom M1 = Nat (Op (->)) (->)
  type Cod M1 = (->)
  type M1 :% f = f :% ()
  M1 % n = n ! Op haskUnit

haskIsTotal :: Adjunction (->) (Nat (Op (->)) (->)) M1 (YonedaEmbedding (->))
haskIsTotal = mkAdjunctionInit M1 YonedaEmbedding
  (\(Nat f _ _) -> Nat f (Hom_X (f % Op haskUnit)) (\_ fz z -> (f % Op (\() -> z)) fz))
  (\_ n fu -> (n ! Op haskUnit) fu ())
