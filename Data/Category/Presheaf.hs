{-# LANGUAGE TypeOperators, TypeFamilies, TypeSynonymInstances, GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Presheaf
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Presheaf where

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Limit
import Data.Category.CartesianClosed
import Data.Category.Yoneda


type Presheaves (~>) = Nat (Op (~>)) (->)

type PShExponential (~>) y z = (Presheaves (~>) :-*: z) :.: Opposite 
  (   ProductFunctor (Presheaves (~>))
  :.: Tuple2 (Presheaves (~>)) (Presheaves (~>)) y
  :.: YonedaEmbedding (~>)
  )
pshExponential :: Category (~>) => Obj (Presheaves (~>)) y -> Obj (Presheaves (~>)) z -> PShExponential (~>) y z
pshExponential y z = hom_X z :.: Opposite (ProductFunctor :.: Tuple2 y :.: yonedaEmbedding)

type instance Exponential (Presheaves (~>)) y z = PShExponential (~>) y z

-- | The category of presheaves on a category @C@ is cartesian closed for any @C@.
instance Category (~>) => CartesianClosed (Presheaves (~>)) where
  
  apply yn@(Nat y _ _) zn@(Nat z _ _) = Nat (pshExponential yn zn :*: y) z (\(Op i) (n, yi) -> (n ! Op i) (i, yi))
  tuple yn zn@(Nat z _ _) = Nat z (pshExponential yn (zn *** yn)) (\(Op i) zi -> (Nat (hom_X i) z (\_ j2i -> (z % Op j2i) zi) *** yn))
  zn ^^^ yn = Nat (pshExponential (tgt yn) (src zn)) (pshExponential (src yn) (tgt zn)) (\(Op i) n -> zn . n . (natId (hom_X i) *** yn))

    
