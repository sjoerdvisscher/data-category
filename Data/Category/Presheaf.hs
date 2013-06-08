{-# LANGUAGE TypeOperators, TypeFamilies, TypeSynonymInstances, GADTs, FlexibleInstances, UndecidableInstances, NoImplicitPrelude #-}
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


type Presheaves k = Nat (Op k) (->)

type PShExponential k y z = (Presheaves k :-*: z) :.: Opposite
  (   ProductFunctor (Presheaves k)
  :.: Tuple2 (Presheaves k) (Presheaves k) y
  :.: YonedaEmbedding k
  )
pshExponential :: Category k => Obj (Presheaves k) y -> Obj (Presheaves k) z -> PShExponential k y z
pshExponential y z = hom_X z :.: Opposite (ProductFunctor :.: tuple2 y :.: yonedaEmbedding)

-- | The category of presheaves on a category @C@ is cartesian closed for any @C@.
instance Category k => CartesianClosed (Presheaves k) where
  type Exponential (Presheaves k) y z = PShExponential k y z
  
  apply yn@(Nat y _ _) zn@(Nat z _ _) = Nat (pshExponential yn zn :*: y) z (\(Op i) (n, yi) -> (n ! Op i) (i, yi))
  tuple yn zn@(Nat z _ _) = Nat z (pshExponential yn (zn *** yn)) (\(Op i) zi -> (Nat (hom_X i) z (\_ j2i -> (z % Op j2i) zi) *** yn))
  zn ^^^ yn = Nat (pshExponential (tgt yn) (src zn)) (pshExponential (src yn) (tgt zn)) (\(Op i) n -> zn . n . (natId (hom_X i) *** yn))

    
