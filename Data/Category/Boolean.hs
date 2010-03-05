{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
module Data.Category.Boolean where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair
import Data.Category.Hask


-- "2", Boolean Category
data family Boolean a b :: *

data Fls = Fls deriving Show
data Tru = Tru deriving Show

data instance Boolean Fls Fls = IdFls
data instance Boolean Tru Tru = IdTru
data instance Boolean Fls Tru = FlsTru

instance Apply Boolean Fls Fls where
  IdFls $$ Fls = Fls
instance Apply Boolean Fls Tru where
  FlsTru $$ Fls = Tru
instance Apply Boolean Tru Tru where
  IdTru $$ Tru = Tru
  
instance CategoryO Boolean Fls where
  id = IdFls
instance CategoryO Boolean Tru where
  id = IdTru

instance CategoryA Boolean Fls Fls Fls where
  IdFls . IdFls = IdFls
instance CategoryA Boolean Fls Fls Tru where
  FlsTru . IdFls = FlsTru  
instance CategoryA Boolean Fls Tru Tru where
  IdTru . FlsTru = FlsTru  
instance CategoryA Boolean Tru Tru Tru where
  IdTru . IdTru = IdTru
  

  
data instance Funct Boolean d (FunctO Boolean d f) (FunctO Boolean d g) = 
  BooleanNat (Component f g Fls) (Component f g Tru)
instance (CategoryO (Cod f) (F f Fls), CategoryO (Cod f) (F f Tru)) => CategoryO (Funct Boolean d) (FunctO Boolean d f) where
  id = BooleanNat id id

initObjInBoolean :: Colimit (VoidF Boolean) Fls
initObjInBoolean = InitialUniversal VoidNat $ BooleanNat (\VoidNat -> IdFls) (\VoidNat -> FlsTru)

termObjInBoolean :: Limit (VoidF Boolean) Tru
termObjInBoolean = TerminalUniversal VoidNat $ BooleanNat (\VoidNat -> FlsTru) (\VoidNat -> IdTru)


type family And x y :: *
type instance And Fls Fls = Fls
type instance And Fls Tru = Fls
type instance And Tru Fls = Fls
type instance And Tru Tru = Tru

prodLimitInBooleanFF :: Limit (PairF Boolean Fls Fls) (And Fls Fls)
prodLimitInBooleanFF = TerminalUniversal (IdFls :***: IdFls) $ BooleanNat (\(f :***: s) -> f) (\(f :***: s) -> s)
prodLimitInBooleanFT :: Limit (PairF Boolean Fls Tru) (And Fls Tru)
prodLimitInBooleanFT = TerminalUniversal (IdFls :***: FlsTru) $ BooleanNat (\(f :***: s) -> f) (\(f :***: s) -> f)
prodLimitInBooleanTF :: Limit (PairF Boolean Tru Fls) (And Tru Fls)
prodLimitInBooleanTF = TerminalUniversal (FlsTru :***: IdFls) $ BooleanNat (\(f :***: s) -> s) (\(f :***: s) -> s)
prodLimitInBooleanTT :: Limit (PairF Boolean Tru Tru) (And Tru Tru)
prodLimitInBooleanTT = TerminalUniversal (IdTru :***: IdTru) $ BooleanNat (\(f :***: s) -> f) (\(f :***: s) -> s)
