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
import Data.Category.NaturalTransformation
import Data.Category.Adjunction


data Representable f repObj = Representable
  { representedFunctor :: f
  , representingObject :: Obj (Dom f) repObj
  , represent          :: forall k z. (Dom f ~ k, Cod f ~ (->)) => Obj k z -> f :% z -> k repObj z
  , universalElement   :: forall k. (Dom f ~ k, Cod f ~ (->)) => f :% repObj
  }

unrepresent :: (Functor f, Dom f ~ k, Cod f ~ (->)) => Representable f repObj -> k repObj z -> f :% z
unrepresent rep h = (representedFunctor rep % h) (universalElement rep)

covariantHomRepr :: Category k => Obj k x -> Representable (x :*-: k) x
covariantHomRepr x = Representable
  { representedFunctor = HomX_ x
  , representingObject = x
  , represent          = \_ h -> h
  , universalElement   = x
  }

contravariantHomRepr :: Category k => Obj k x -> Representable (k :-*: x) x
contravariantHomRepr x = Representable
  { representedFunctor = Hom_X x
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
  { representedFunctor = HomX_ (src mor) :.: u
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
  { representedFunctor = Hom_X (tgt mor) :.: Opposite u
  , representingObject = Op obj
  , represent          = \(Op y) f -> Op (factorizer y f)
  , universalElement   = mor
  }


-- | For an adjunction F -| G, each pair (FY, unit_Y) is an initial morphism from Y to G.
adjunctionInitialProp :: Adjunction c d f g -> Obj d y -> InitialUniversal y g (f :% y)
adjunctionInitialProp adj@(Adjunction f g _ _) y = initialUniversal g (f % y) (adjunctionUnit adj ! y) (rightAdjunct adj)

-- | For an adjunction F -| G, each pair (GX, counit_X) is a terminal morphism from F to X.
adjunctionTerminalProp :: Adjunction c d f g -> Obj c x -> TerminalUniversal x f (g :% x)
adjunctionTerminalProp adj@(Adjunction f g _ _) x = terminalUniversal f (g % x) (adjunctionCounit adj ! x) (leftAdjunct adj)


initialPropAdjunction :: forall f g c d. (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall y. InitialUniversal y g (f :% y)) -> Adjunction c d f g
initialPropAdjunction f g univ = mkAdjunctionInit f g (\_ -> universalElement univ) (represent univ)

terminalPropAdjunction :: forall f g c d. (Functor f, Functor g, Dom f ~ d, Cod f ~ c, Dom g ~ c, Cod g ~ d)
  => f -> g -> (forall x. TerminalUniversal x f (g :% x)) -> Adjunction c d f g
terminalPropAdjunction f g univ = mkAdjunctionTerm f g ((unOp .) . represent univ . Op) (\_ -> universalElement univ)
