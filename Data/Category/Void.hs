{-# LANGUAGE TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Category.Void where

import Data.Category
import Data.Category.Functor

-- Void, the empty category
data family Void a b :: *

data instance Funct Void d (FunctO Void d f) (FunctO Void d g) = 
  VoidNat
instance CategoryO (Funct Void d) (FunctO Void d f) where
  id = VoidNat
instance (CategoryO (~>) a, CategoryO (~>) b) => FunctorA (Diag Void (~>)) a b where
  Diag % f = VoidNat

data VoidF ((~>) :: * -> * -> *) = VoidF
type instance Dom (VoidF (~>)) = Void
type instance Cod (VoidF (~>)) = (~>)

class VoidColimit (~>) where
  type InitialObject (~>) :: *
  voidColimit :: Colimit (VoidF (~>)) (InitialObject (~>))
class VoidLimit (~>) where
  type TerminalObject (~>) :: *
  voidLimit :: Limit (VoidF (~>)) (TerminalObject (~>))
