{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
module Data.Category.Boolean where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Functor
import Data.Category.Void
import Data.Category.Pair


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
  BooleanNat { flsComp :: Component f g Fls, truComp :: Component f g Tru }
instance (CategoryO (Cod f) (F f Fls), CategoryO (Cod f) (F f Tru)) => CategoryO (Funct Boolean d) (FunctO Boolean d f) where
  id = BooleanNat id id

instance VoidColimit Boolean where
  type InitialObject Boolean = Fls
  voidColimit = InitialUniversal VoidNat (BooleanNat (\VoidNat -> IdFls) (\VoidNat -> FlsTru))
instance VoidLimit Boolean where
  type TerminalObject Boolean = Tru
  voidLimit = TerminalUniversal VoidNat (BooleanNat (\VoidNat -> FlsTru) (\VoidNat -> IdTru))

instance PairLimit Boolean Fls Fls where 
  type Product Fls Fls = Fls
  pairLimit = TerminalUniversal (IdFls :***: IdFls) (BooleanNat fstComp sndComp)
instance PairLimit Boolean Fls Tru where 
  type Product Fls Tru = Fls
  pairLimit = TerminalUniversal (IdFls :***: FlsTru) (BooleanNat fstComp fstComp)
instance PairLimit Boolean Tru Fls where 
  type Product Tru Fls = Fls
  pairLimit = TerminalUniversal (FlsTru :***: IdFls) (BooleanNat sndComp sndComp)
instance PairLimit Boolean Tru Tru where 
  type Product Tru Tru = Tru
  pairLimit = TerminalUniversal (IdTru :***: IdTru) (BooleanNat fstComp sndComp)

instance PairColimit Boolean Fls Fls where 
  type Coproduct Fls Fls = Fls
  pairColimit = InitialUniversal (IdFls :***: IdFls) (BooleanNat fstComp sndComp)
instance PairColimit Boolean Fls Tru where 
  type Coproduct Fls Tru = Tru
  pairColimit = InitialUniversal (FlsTru :***: IdTru) (BooleanNat sndComp sndComp)
instance PairColimit Boolean Tru Fls where 
  type Coproduct Tru Fls = Tru
  pairColimit = InitialUniversal (IdTru :***: FlsTru) (BooleanNat fstComp fstComp)
instance PairColimit Boolean Tru Tru where 
  type Coproduct Tru Tru = Tru
  pairColimit = InitialUniversal (IdTru :***: IdTru) (BooleanNat fstComp sndComp)
