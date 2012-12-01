{-# LANGUAGE TypeOperators, RankNTypes, TypeFamilies, NoImplicitPrelude #-}
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

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.CartesianClosed

type YonedaEmbedding k = Postcompose (Hom k) (Op k) :.: ToTuple2 k (Op k) 

-- | The Yoneda embedding functor, @C -> Set^(C^op)@.
yonedaEmbedding :: Category k => YonedaEmbedding k
yonedaEmbedding = Postcompose Hom :.: ToTuple2


data Yoneda (k :: * -> * -> *) f = Yoneda
type instance Dom (Yoneda k f) = Op k
type instance Cod (Yoneda k f) = (->)
type instance Yoneda k f :% a = Nat (Op k) (->) (k :-*: a) f
-- | 'Yoneda' converts a functor @f@ into a natural transformation from the hom functor to f.
instance (Category k, Functor f, Dom f ~ Op k, Cod f ~ (->)) => Functor (Yoneda k f) where
  Yoneda % Op ab = \n -> n . yonedaEmbedding % ab
      
  
-- | 'fromYoneda' and 'toYoneda' are together the isomophism from the Yoneda lemma.
fromYoneda :: (Category k, Functor f, Dom f ~ Op k, Cod f ~ (->)) => f -> Yoneda k f :~> f
fromYoneda f = Nat Yoneda f (\(Op a) n -> (n ! Op a) a)

toYoneda   :: (Category k, Functor f, Dom f ~ Op k, Cod f ~ (->)) => f -> f :~> Yoneda k f
toYoneda   f = Nat f Yoneda (\(Op a) fa -> Nat (hom_X a) f (\_ h -> (f % Op h) fa))
