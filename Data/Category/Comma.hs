{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, GADTs, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Comma
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Comma categories.
-----------------------------------------------------------------------------
module Data.Category.Comma where

import Data.Kind (Type)

import Data.Category
import Data.Category.Adjunction
import Data.Category.Functor
import Data.Category.Limit
import Data.Category.RepresentableFunctor


data CommaO :: Type -> Type -> Type -> Type where
  CommaO :: (Cod t ~ k, Cod s ~ k)
    => Obj (Dom t) a -> k (t :% a) (s :% b) -> Obj (Dom s) b -> CommaO t s (a, b)

data (:/\:) :: Type -> Type -> Type -> Type -> Type where
  CommaA ::
    CommaO t s (a, b) ->
    Dom t a a' ->
    Dom s b b' ->
    CommaO t s (a', b') ->
    (t :/\: s) (a, b) (a', b')

commaId :: CommaO t s (a, b) -> Obj (t :/\: s) (a, b)
commaId o@(CommaO a _ b) = CommaA o a b o

-- | The comma category T \\downarrow S
instance (Category (Dom t), Category (Dom s)) => Category (t :/\: s) where

  src (CommaA so _ _ _) = commaId so
  tgt (CommaA _ _ _ to) = commaId to

  (CommaA _ g h to) . (CommaA so g' h' _) = CommaA so (g . g') (h . h') to


type (f `ObjectsFUnder` a) = ConstF f a :/\: f
type (f `ObjectsFOver`  a) = f :/\: ConstF f a

type (c `ObjectsUnder` a) = Id c `ObjectsFUnder` a
type (c `ObjectsOver`  a) = Id c `ObjectsFOver`  a


initialUniversalComma :: forall u x c a a_
                       . (Functor u, c ~ (u `ObjectsFUnder` x), HasInitialObject c, (a_, a) ~ InitialObject c)
                      => u -> InitialUniversal x u a
initialUniversalComma u = case initialObject :: Obj c (a_, a) of
  CommaA (CommaO _ mor a) _ _ _ ->
    initialUniversal u a mor factorizer
      where
        factorizer :: forall y. Obj (Dom u) y -> Cod u x (u :% y) -> Dom u a y
        factorizer y arr = case init (commaId (CommaO y arr y)) of CommaA _ _ f _ -> f
          where
            init :: Obj c (y, y) -> c (a_, a) (y, y)
            init = initialize

terminalUniversalComma :: forall u x c a a_
                        . (Functor u, c ~ (u `ObjectsFOver` x), HasTerminalObject c, (a, a_) ~ TerminalObject c)
                       => u -> TerminalUniversal x u a
terminalUniversalComma u = case terminalObject :: Obj c (a, a_) of
  CommaA (CommaO a mor _) _ _ _ ->
    terminalUniversal u a mor factorizer
      where
        factorizer :: forall y. Obj (Dom u) y -> Cod u (u :% y) x -> Dom u y a
        factorizer y arr = case term (commaId (CommaO y arr y)) of CommaA _ f _ _ -> f
          where
            term :: Obj c (y, y) -> c (y, y) (a, a_)
            term = terminate


type Arrows k = Id k :/\: Id k

data IdArrow (k :: Type -> Type -> Type) = IdArrow
instance Category k => Functor (IdArrow k) where
  type Dom (IdArrow k) = k
  type Cod (IdArrow k) = Arrows k
  type IdArrow k :% a = (a, a)
  IdArrow % f = CommaA
    (CommaO (src f) (src f) (src f))
    f
    f
    (CommaO (tgt f) (tgt f) (tgt f))

data Src (k :: Type -> Type -> Type) = Src
instance Category k => Functor (Src k) where
  type Dom (Src k) = Arrows k
  type Cod (Src k) = k
  type Src k :% (a, b) = a
  Src % (CommaA _ aa' _ _) = aa'

data Tgt (k :: Type -> Type -> Type) = Tgt
instance Category k => Functor (Tgt k) where
  type Dom (Tgt k) = Arrows k
  type Cod (Tgt k) = k
  type Tgt k :% (a, b) = b
  Tgt % (CommaA _ _ bb' _) = bb'

-- | Taking the target of an arrow is left adjoint to taking the identity of an object
tgtIdAdj :: Category k => Adjunction k (Arrows k) (Tgt k) (IdArrow k)
tgtIdAdj = mkAdjunctionUnits Tgt IdArrow (\(CommaA o@(CommaO _ ab b) _ _ _) -> CommaA o ab b (CommaO b b b)) (\o -> o)

-- | Taking the source of an arrow is right adjoint to taking the identity of an object
idSrcAdj :: Category k => Adjunction (Arrows k) k (IdArrow k) (Src k)
idSrcAdj = mkAdjunctionUnits IdArrow Src (\o -> o) (\(CommaA o@(CommaO a ab _) _ _ _) -> CommaA (CommaO a a a) a ab o)