{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Functor
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Functor where
  
import Data.Category


-- | Functor category Funct(C, D), or D^C.
-- Objects of Funct(C, D) are functors from C to D.
-- Arrows of Funct(C, D) are natural transformations.
-- Each category C needs its own data instance.



-- | Arrows of the category Funct(Funct(C, D), E)
-- I.e. natural transformations between functors of type D^C -> E
data instance Nat (Nat c d) e f g = 
  FunctNat { unFunctNat :: forall h. (Dom h ~ c, Cod h ~ d) => Obj h -> Component f g h }



-- | The diagonal functor from (index-) category J to (~>).
data Diag (j :: * -> * -> *) ((~>) :: * -> * -> *) = Diag
type instance Dom (Diag j (~>)) = (~>)
type instance Cod (Diag j (~>)) = Nat j (~>)
type instance F (Diag j (~>)) a = Const j (~>) a

type Limit   f l = TerminalUniversal f (Diag (Dom f) (Cod f)) l
type Colimit f l = InitialUniversal  f (Diag (Dom f) (Cod f)) l