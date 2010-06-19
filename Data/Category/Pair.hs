{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, EmptyDataDecls, ScopedTypeVariables, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Pair
-- Copyright   :  (c) Sjoerd Visscher 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Pair, the category with just 2 objects and their identity arrows.
-- The limit and colimit of the functor from Pair to some category provide 
-- products and coproducts in that category.
-----------------------------------------------------------------------------
module Data.Category.Pair where

import Prelude hiding ((.), id, Functor, product)
import qualified Control.Arrow as A ((&&&), (***), (|||), (+++))

import Data.Category
import Data.Category.Functor
import Data.Category.NaturalTransformation
import Data.Category.Adjunction
import Data.Category.Product


data P1
data P2

-- | The arrows of Pair.
data Pair :: * -> * -> * where
  IdFst :: Pair P1 P1
  IdSnd :: Pair P2 P2

instance Category Pair where
  
  data Obj Pair a where
    Fst :: Obj Pair P1
    Snd :: Obj Pair P2
  
  src IdFst = Fst
  src IdSnd = Snd
  
  tgt IdFst = Fst
  tgt IdSnd = Snd
  
  id  Fst       = IdFst
  id  Snd       = IdSnd
  
  IdFst . IdFst = IdFst
  IdSnd . IdSnd = IdSnd
  _     . _     = undefined -- this can't happen


-- | The functor from Pair to (~>), a diagram of 2 objects in (~>).
data PairF :: (* -> * -> *) -> * -> * -> * where
  PairF :: Category (~>) => Obj (~>) x -> Obj (~>) y -> PairF (~>) x y
type instance Dom (PairF (~>) x y) = Pair
type instance Cod (PairF (~>) x y) = (~>)
type instance F (PairF (~>) x y) P1 = x
type instance F (PairF (~>) x y) P2 = y
instance Functor (PairF (~>) x y) where
  PairF x _ %% Fst = x
  PairF _ y %% Snd = y
  PairF x _ % IdFst = id x
  PairF _ y % IdSnd = id y


pairNat :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
  => f -> g -> Comp f g P1 -> Comp f g P2 -> Nat Pair d f g
pairNat f g c1 c2 = Nat f g (\x -> unCom $ n c1 c2 x) where
  n :: (Functor f, Functor g, Dom f ~ Pair, Cod f ~ d, Dom g ~ Pair, Cod g ~ d) 
    => Comp f g P1 -> Comp f g P2 -> Obj Pair a -> Comp f g a
  n c _ Fst = c
  n _ c Snd = c
  

-- | The product of 2 objects is the limit of the functor from Pair to (~>).
type family Product ((~>) :: * -> * -> *) x y :: *
class Category (~>) => PairLimit (~>) where
  
  pairLimit :: Obj (~>) x -> Obj (~>) y -> Limit (PairF (~>) x y) (Product (~>) x y)
  pairLimit x y = TerminalUniversal
    (product x y)
    (pairNat (Const $ product x y) (PairF x y) (Com $ fst $ proj x y) (Com $ snd $ proj x y)) 
    (\_ n -> (n ! Fst) &&& (n ! Snd))

  product :: Obj (~>) x -> Obj (~>) y -> Obj (~>) (Product (~>) x y)
  product x y = limitObject $ pairLimit x y
  
  proj :: Obj (~>) x -> Obj (~>) y -> (Product (~>) x y ~> x, Product (~>) x y ~> y)
  proj x y = (n ! Fst, n ! Snd) where 
    n = terminalMorphism $ pairLimit x y

  (&&&) :: (a ~> x) -> (a ~> y) -> (a ~> Product (~>) x y)
  l &&& r = n (src l) (pairNat undefined undefined (Com l) (Com r)) where
    n = terminalFactorizer $ pairLimit (tgt l) (tgt r)

  (***) :: (a1 ~> b1) -> (a2 ~> b2) -> (Product (~>) a1 a2 ~> Product (~>) b1 b2)
  l *** r = (l . proj1) &&& (r . proj2) where
    (proj1, proj2) = proj (src l) (src r)


-- | The coproduct of 2 objects is the colimit of the functor from Pair to (~>).
type family Coproduct ((~>) :: * -> * -> *) x y :: *
class Category (~>) => PairColimit (~>) where

  pairColimit :: Obj (~>) x -> Obj (~>) y -> Colimit (PairF (~>) x y) (Coproduct (~>) x y)
  pairColimit x y = InitialUniversal 
    (coproduct x y) 
    (pairNat (PairF x y) (Const $ coproduct x y) (Com $ fst $ inj x y) (Com $ snd $ inj x y)) 
    (\_ n -> (n ! Fst) ||| (n ! Snd))
  
  coproduct :: Obj (~>) x -> Obj (~>) y -> Obj (~>) (Coproduct (~>) x y)
  coproduct x y = colimitObject $ pairColimit x y
  
  inj :: Obj (~>) x -> Obj (~>) y -> (x ~> Coproduct (~>) x y, y ~> Coproduct (~>) x y)
  inj x y = (n ! Fst, n ! Snd) where 
    n = initialMorphism $ pairColimit x y

  (|||) :: (x ~> a) -> (y ~> a) -> (Coproduct (~>) x y ~> a)
  l ||| r = n (tgt l) (pairNat undefined undefined (Com l) (Com r)) where
    n = initialFactorizer $ pairColimit (src l) (src r)
    
  (+++) :: (a1 ~> b1) -> (a2 ~> b2) -> (Coproduct (~>) a1 a2 ~> Coproduct (~>) b1 b2)
  l +++ r = (inj1 . l) ||| (inj2 . r) where
    (inj1, inj2) = inj (tgt l) (tgt r)
    

type instance Product (->) x y = (x, y)

instance PairLimit (->) where
  
  product HaskO HaskO = HaskO
  
  proj _ _ = (fst, snd)
  
  (&&&) = (A.&&&)
  (***) = (A.***)


type instance Coproduct (->) x y = Either x y

instance PairColimit (->) where
  
  coproduct HaskO HaskO = HaskO
  
  inj _ _ = (Left, Right)
  
  (|||) = (A.|||)
  (+++) = (A.+++)
  
  
type instance Product Cat (CatW c1) (CatW c2) = CatW (c1 :*: c2)

instance PairLimit Cat where
  
  product CatO CatO = CatO
  
  proj CatO CatO = (CatA Proj1, CatA Proj2)
  
  CatA f1 &&& CatA f2 = CatA ((f1 :***: f2) :.: DiagProd)
  CatA f1 *** CatA f2 = CatA (f1 :***: f2)


-- | Functor product
data Prod ((~>) :: * -> * -> *) = Prod

type instance Dom (Prod (~>)) = Nat Pair (~>)
type instance Cod (Prod (~>)) = (~>)
type instance F (Prod (~>)) f = Product (~>) (F f P1) (F f P2)

instance PairLimit (~>) => Functor (Prod (~>)) where
  Prod %% NatO f   = (f %% Fst) `product` (f %% Snd)
  Prod % Nat _ _ n = n Fst      ***       n Snd

-- prodAdj :: PairLimit (~>) => Adjunction (Nat Pair (~>)) (~>) (Diag Pair (~>)) (Prod (~>))
-- prodAdj = Adjunction Diag Prod
--   (Nat Id (Prod :.: Diag) $ \x -> id x &&& id x)
--   (Nat (Diag :.: Prod) Id $ h)
--     where 
--       h :: PairLimit (~>) => Obj (Nat Pair (~>)) a -> Nat Pair (~>) (Const Pair (~>) (Product (~>) (F a P1) (F a P2))) a
--       h (NatO f) = terminalMorphism $ pairLimit (f %% Fst) (f %% Snd)
        -- Nat (Const (Prod %% NatO f)) f (\n -> (terminalMorphism $ pairLimit (f %% Fst) (f %% Snd)) ! n)
  
-- { unit = Nat $ \_ -> id A.&&& id, counit = Nat $ \_ -> fromPairNat (fst :***: snd) }

-- data (:*:) :: * -> * -> * where
--   (:*:) :: (Dom f ~ Dom g, Cod f ~ Cod g) => f -> g -> f :*: g
-- type instance Dom (f :*: g) = Dom f
-- type instance Cod (f :*: g) = Cod f
-- type instance F (f :*: g) x = Product (F f x) (F g x)
-- instance ()
--   => FunctorA (g :*: h) a b where
--   _ % f = ((obj :: g) % f) &&& ((obj :: h) % f)
-- 
-- -- | Functor coproduct
-- data f :+: g = f :+: g
-- type instance Dom (f :+: g) = Dom f -- ~ Dom g
-- type instance Cod (f :+: g) = Cod f -- ~ Cod g
-- type instance F (f :+: g) x = Coproduct (F f x) (F g x)
