{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Boolean
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- /2/, or the Boolean category. 
-- It contains 2 objects, one for true and one for false.
-- It contains 3 arrows, 2 identity arrows and one from false to true.
-----------------------------------------------------------------------------
module Data.Category.Boolean where

import Prelude hiding ((.), id)

import Data.Category
import Data.Category.Void
import Data.Category.Pair

-- | 'Fls', the object representing false.
data Fls = Fls deriving Show
-- | 'Tru', the object representing true.
data Tru = Tru deriving Show

-- | The arrows of the boolean category.
data family Boolean a b :: *
data instance Boolean Fls Fls = IdFls
data instance Boolean Tru Tru = IdTru
data instance Boolean Fls Tru = FlsTru

data instance Nat Boolean d f g = 
  BooleanNat (Component f g Fls) (Component f g Tru)

instance Category Boolean where
  idNat = BooleanNat IdFls IdTru
instance CategoryO Boolean Fls where
  BooleanNat f _ ! Fls = f
instance CategoryO Boolean Tru where
  BooleanNat _ t ! Tru = t

instance CategoryA Boolean Fls Fls Fls where
  IdFls . IdFls = IdFls
instance CategoryA Boolean Fls Fls Tru where
  FlsTru . IdFls = FlsTru  
instance CategoryA Boolean Fls Tru Tru where
  IdTru . FlsTru = FlsTru  
instance CategoryA Boolean Tru Tru Tru where
  IdTru . IdTru = IdTru
    
instance Apply Boolean Fls Fls where
  IdFls $$ Fls = Fls
instance Apply Boolean Fls Tru where
  FlsTru $$ Fls = Tru
instance Apply Boolean Tru Tru where
  IdTru $$ Tru = Tru
  


instance VoidColimit Boolean where
  type InitialObject Boolean = Fls
  voidColimit = InitialUniversal VoidNat (BooleanNat (\VoidNat -> IdFls) (\VoidNat -> FlsTru))
instance VoidLimit Boolean where
  type TerminalObject Boolean = Tru
  voidLimit = TerminalUniversal VoidNat (BooleanNat (\VoidNat -> FlsTru) (\VoidNat -> IdTru))

instance PairLimit Boolean Fls Fls where 
  type Product Fls Fls = Fls
  pairLimit = TerminalUniversal (IdFls :***: IdFls) (BooleanNat (! Fst) (! Snd))
instance PairLimit Boolean Fls Tru where 
  type Product Fls Tru = Fls
  pairLimit = TerminalUniversal (IdFls :***: FlsTru) (BooleanNat (! Fst) (! Fst))
instance PairLimit Boolean Tru Fls where 
  type Product Tru Fls = Fls
  pairLimit = TerminalUniversal (FlsTru :***: IdFls) (BooleanNat (! Snd) (! Snd))
instance PairLimit Boolean Tru Tru where 
  type Product Tru Tru = Tru
  pairLimit = TerminalUniversal (IdTru :***: IdTru) (BooleanNat (! Fst) (! Snd))

instance PairColimit Boolean Fls Fls where 
  type Coproduct Fls Fls = Fls
  pairColimit = InitialUniversal (IdFls :***: IdFls) (BooleanNat (! Fst) (! Snd))
instance PairColimit Boolean Fls Tru where 
  type Coproduct Fls Tru = Tru
  pairColimit = InitialUniversal (FlsTru :***: IdTru) (BooleanNat (! Snd) (! Snd))
instance PairColimit Boolean Tru Fls where 
  type Coproduct Tru Fls = Tru
  pairColimit = InitialUniversal (IdTru :***: FlsTru) (BooleanNat (! Fst) (! Fst))
instance PairColimit Boolean Tru Tru where 
  type Coproduct Tru Tru = Tru
  pairColimit = InitialUniversal (IdTru :***: IdTru) (BooleanNat (! Fst) (! Snd))
