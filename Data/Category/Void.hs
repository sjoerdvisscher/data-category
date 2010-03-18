{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, EmptyDataDecls, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Void
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- /0/, the empty category. 
-- The limit and colimit of the functor from /0/ to some category provide 
-- terminal and initial objects in that category.
-----------------------------------------------------------------------------
module Data.Category.Void where

import Data.Category
import Data.Category.Functor

-- | The (empty) data type of the arrows in /0/. 
data Void a b

data instance Funct Void d f g = 
  VoidNat
instance CategoryO (Funct Void d) f where
  id = VoidNat
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag Void (~>)) a b where
  Diag % _ = VoidNat

-- | The functor from /0/ to (~>), the empty diagram in (~>).
data VoidF ((~>) :: * -> * -> *) = VoidF
type instance Dom (VoidF (~>)) = Void
type instance Cod (VoidF (~>)) = (~>)

-- | An initial object is the colimit of the functor from /0/ to (~>).
class VoidColimit (~>) where
  type InitialObject (~>) :: *
  voidColimit :: Colimit (VoidF (~>)) (InitialObject (~>))
  initialize :: GetComponent (~>) (->) a => InitialObject (~>) ~> a
  initialize = (n ! (obj :: a)) VoidNat where 
    InitialUniversal VoidNat n = voidColimit
  
-- | A terminal object is the limit of the functor from /0/ to (~>).
class VoidLimit (~>) where
  type TerminalObject (~>) :: *
  voidLimit :: Limit (VoidF (~>)) (TerminalObject (~>))
  terminate :: GetComponent (~>) (->) a => a ~> TerminalObject (~>)
  terminate = (n ! (obj :: a)) VoidNat where
    TerminalUniversal VoidNat n = voidLimit
