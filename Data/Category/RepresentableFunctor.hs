{-# LANGUAGE TypeOperators, TypeFamilies, RankNTypes, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.RepresentableFunctor
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.RepresentableFunctor where

import Data.Category
import Data.Category.Functor


data Representable f repObj = Representable
  { representedFunctor :: f
  , representingObject :: Obj (Dom f) repObj
  , represent          :: (Dom f ~ k, Cod f ~ (->)) => Obj k z -> f :% z -> k repObj z
  , universalElement   :: (Dom f ~ k, Cod f ~ (->)) => f :% repObj
  }

unrepresent :: (Functor f, Dom f ~ k, Cod f ~ (->)) => Representable f repObj -> k repObj z -> f :% z
unrepresent rep h = (representedFunctor rep % h) (universalElement rep)

covariantHomRepr :: Category k => Obj k x -> Representable (x :*-: k) x
covariantHomRepr x = Representable
  { representedFunctor = homX_ x
  , representingObject = x
  , represent          = \_ h -> h
  , universalElement   = x
  }

contravariantHomRepr :: Category k => Obj k x -> Representable (k :-*: x) x
contravariantHomRepr x = Representable
  { representedFunctor = hom_X x
  , representingObject = Op x
  , represent          = \_ h -> Op h
  , universalElement   = x
  }

type InitialUniversal x u a = Representable ((x :*-: Cod u) :.: u) a
-- | An initial universal property, a universal morphism from x to u.
initialUniversal :: Functor u
                 => u 
                 -> Obj (Dom u) a 
                 -> Cod u x (u :% a) 
                 -> (forall y. Obj (Dom u) y -> Cod u x (u :% y) -> Dom u a y) 
                 -> InitialUniversal x u a
initialUniversal u obj mor factorizer = Representable
  { representedFunctor = homX_ (src mor) :.: u
  , representingObject = obj
  , represent          = factorizer
  , universalElement   = mor
  }
  
type TerminalUniversal x u a = Representable ((Cod u :-*: x) :.: Opposite u) a
-- | A terminal universal property, a universal morphism from u to x.
terminalUniversal :: Functor u
                  => u 
                  -> Obj (Dom u) a
                  -> Cod u (u :% a) x
                  -> (forall y. Obj (Dom u) y -> Cod u (u :% y) x -> Dom u y a) 
                  -> TerminalUniversal x u a
terminalUniversal u obj mor factorizer = Representable
  { representedFunctor = hom_X (tgt mor) :.: Opposite u
  , representingObject = Op obj
  , represent          = \(Op y) f -> Op (factorizer y f)
  , universalElement   = mor
  }
