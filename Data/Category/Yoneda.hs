{-# LANGUAGE TypeOperators, TypeFamilies #-}
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

type YonedaEmbedding (~>) = Postcompose (Hom (~>)) (Op (~>)) :.: ToTuple2 (~>) (Op (~>)) 

-- | The Yoneda embedding functor, @C -> Set^(C^op)@.
yonedaEmbedding :: Category (~>) => YonedaEmbedding (~>)
yonedaEmbedding = Postcompose Hom :.: ToTuple2


data Yoneda ((~>) :: * -> * -> *) f = Yoneda
type instance Dom (Yoneda (~>) f) = Op (~>)
type instance Cod (Yoneda (~>) f) = (->)
type instance Yoneda (~>) f :% a = Nat (Op (~>)) (->) ((~>) :-*: a) f
-- | 'Yoneda' converts a functor @f@ into a natural transformation from the hom functor to f.
instance (Category (~>), Functor f, Dom f ~ Op (~>), Cod f ~ (->)) => Functor (Yoneda (~>) f) where
  Yoneda % Op ab = \n -> n . yonedaEmbedding % ab
      
  
-- | 'fromYoneda' and 'toYoneda' are together the isomophism from the Yoneda lemma.
fromYoneda :: (Category (~>), Functor f, Dom f ~ Op (~>), Cod f ~ (->)) => f -> Yoneda (~>) f :~> f
fromYoneda f = Nat Yoneda f (\(Op a) n -> (n ! Op a) a)

toYoneda   :: (Category (~>), Functor f, Dom f ~ Op (~>), Cod f ~ (->)) => f -> f :~> Yoneda (~>) f
toYoneda   f = Nat f Yoneda (\(Op a) fa -> Nat (hom_X a) f (\_ h -> (f % Op h) fa))
