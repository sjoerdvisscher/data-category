{-# LANGUAGE TypeOperators, TypeFamilies, RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.RepresentableFunctor
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.RepresentableFunctor where

import Prelude (($), id)

import Data.Category
import Data.Category.Functor


data Representation f repObj = Representation
  { representedFunctor :: f
  , representingObject :: Obj (Dom f) repObj
  , represent          :: (Dom f ~ (~>), Cod f ~ (->)) => Obj (~>) z -> f :% z -> repObj ~> z
  , universalElement   :: (Dom f ~ (~>), Cod f ~ (->)) => f :% repObj
  }

unrepresent :: (Functor f, Dom f ~ (~>), Cod f ~ (->)) => Representation f repObj -> repObj ~> z -> f :% z
unrepresent rep h = representedFunctor rep % h $ universalElement rep

covariantHomRepr :: Category (~>) => Obj (~>) x -> Representation (x :*-: (~>)) x
covariantHomRepr x = Representation
  { representedFunctor = homX_ x
  , representingObject = x
  , represent          = \_ -> id
  , universalElement   = x
  }

contravariantHomRepr :: Category (~>) => Obj (~>) x -> Representation ((~>) :-*: x) x
contravariantHomRepr x = Representation
  { representedFunctor = hom_X x
  , representingObject = Op x
  , represent          = \_ h -> Op h
  , universalElement   = x
  }

type InitialUniversal x u a = Representation ((x :*-: Cod u) :.: u) a
-- | An initial universal property, a universal morphism from x to u.
initialUniversal :: Functor u
                 => u 
                 -> Obj (Dom u) a 
                 -> Cod u x (u :% a) 
                 -> (forall y. Obj (Dom u) y -> Cod u x (u :% y) -> Dom u a y) 
                 -> InitialUniversal x u a
initialUniversal u obj mor factorizer = Representation
  { representedFunctor = homX_ (src mor) :.: u
  , representingObject = obj
  , represent          = factorizer
  , universalElement   = mor
  }
  
type TerminalUniversal x u a = Representation ((Cod u :-*: x) :.: Opposite u) a
-- | A terminal universal property, a universal morphism from u to x.
terminalUniversal :: Functor u
                  => u 
                  -> Obj (Dom u) a
                  -> Cod u (u :% a) x
                  -> (forall y. Obj (Dom u) y -> Cod u (u :% y) x -> Dom u y a) 
                  -> TerminalUniversal x u a
terminalUniversal u obj mor factorizer = Representation
  { representedFunctor = hom_X (tgt mor) :.: Opposite u
  , representingObject = Op obj
  , represent          = \(Op y) f -> Op (factorizer y f)
  , universalElement   = mor
  }
