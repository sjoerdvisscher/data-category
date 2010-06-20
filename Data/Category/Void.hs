{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleInstances, FlexibleContexts, GADTs, EmptyDataDecls #-}
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

import Prelude hiding ((.), id, Functor)
import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Unit

-- | The (empty) data type of the arrows in /0/. 
data Void a b

magicVoid :: Void a b -> x
magicVoid x = x `seq` error "we never get this far"

magicVoidO :: Obj Void a -> x
magicVoidO x = x `seq` error "we never get this far"


instance Category Void where
  
  -- | The (empty) data type of the objects in /0/. 
  data Obj Void a
  
  src = magicVoid
  tgt = magicVoid
  
  id    = magicVoidO
  a . b = magicVoid (a `seq` b)


-- | The functor from /0/ to (~>), the empty diagram in (~>).
data VoidF ((~>) :: * -> * -> *) = VoidF
type instance Dom (VoidF (~>)) = Void
type instance Cod (VoidF (~>)) = (~>)
instance Functor (VoidF (~>)) where 
  VoidF %% x = magicVoidO x
  VoidF %  f = magicVoid f


voidNat :: (Functor f, Functor g, Dom f ~ Void, Dom g ~ Void, Cod f ~ d, Cod g ~ d)
  => f -> g -> Nat Void d f g
voidNat f g = Nat f g magicVoidO



-- | An initial object is the colimit of the functor from /0/ to (~>).
class Category (~>) => VoidColimit (~>) where
  
  type InitialObject (~>) :: *
  
  voidColimit :: Colimit (VoidF (~>)) (InitialObject (~>))
  voidColimit = InitialUniversal 
    initialObject
    (voidNat VoidF (Const initialObject)) 
    (\a _ -> initialize a)

  initialObject :: Obj (~>) (InitialObject (~>))
  initialObject = iuObject voidColimit

  initialize :: Obj (~>) a -> InitialObject (~>) ~> a
  initialize a = initialFactorizer voidColimit a (voidNat VoidF (Const a))


type instance F (ColimitFunctor Void (~>)) f = InitialObject (~>)

instance VoidColimit (~>) => Functor (ColimitFunctor Void (~>)) where
  ColimitFunctor %% _ = initialObject
  ColimitFunctor %  _ = initialize initialObject
  

-- | A terminal object is the limit of the functor from /0/ to (~>).
class Category (~>) => VoidLimit (~>) where
  
  type TerminalObject (~>) :: *
  
  voidLimit :: Limit (VoidF (~>)) (TerminalObject (~>))
  voidLimit = TerminalUniversal 
    terminalObject
    (voidNat (Const terminalObject) VoidF)
    (\a _ -> terminate a)

  terminalObject :: Obj (~>) (TerminalObject (~>))
  terminalObject = tuObject voidLimit
  
  terminate :: Obj (~>) a -> a ~> TerminalObject (~>)
  terminate a = terminalFactorizer voidLimit a (voidNat (Const a) VoidF)


type instance F (LimitFunctor Void (~>)) f = TerminalObject (~>)

instance VoidLimit (~>) => Functor (LimitFunctor Void (~>)) where
  LimitFunctor %% _ = terminalObject
  LimitFunctor %  _ = terminate terminalObject


-- | Any empty data type is an initial object in Hask.
data Zero

instance VoidColimit (->) where
  
  type InitialObject (->) = Zero
  
  initialObject = HaskO
  
  -- With thanks to Conor McBride
  initialize HaskO x = x `seq` error "we never get this far"

instance VoidLimit (->) where
  
  type TerminalObject (->) = ()
  
  terminalObject = HaskO
  
  terminate HaskO _ = ()


instance VoidColimit Cat where
  
  type InitialObject Cat = CatW Void
  
  initialObject = CatO
  
  initialize CatO = CatA VoidF

instance VoidLimit Cat where
  
  type TerminalObject Cat = CatW Unit
  
  terminalObject = CatO
  
  terminate CatO = CatA $ Const UnitO
