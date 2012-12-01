{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, TypeFamilies, UndecidableInstances, RankNTypes, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.AddObject
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.AddObject where
  
import Data.Category
import Data.Category.Functor
import Data.Category.Limit

data O
data I
data T
data N
data C n


data Lift f k = Lift (forall a b. k a b -> f k (C a) (C b))

type instance Dom (Lift f k) = k
type instance Cod (Lift f k) = f k
type instance Lift f k :% a = C a
instance (Category k, Category (f k)) => Functor (Lift f k) where
  Lift copy % f = copy f
  

data AddObject c a b where
  Object :: AddObject c O O
  CopyO :: c a b -> AddObject c (C a) (C b)

-- | `AddObject c` takes an existing category `c` and adds one object that has no arrows to any other object.
instance Category c => Category (AddObject c) where
  
  src Object = Object
  src (CopyO a) = CopyO (src a)
  
  tgt Object = Object
  tgt (CopyO a) = CopyO (tgt a)
  
  Object . Object = Object
  CopyO a . CopyO b = CopyO (a . b)

liftO :: Lift AddObject k
liftO = Lift CopyO


data AddInit c a b where
  InitO ::            AddInit c  I     I
  InitC :: Obj c a -> AddInit c  I    (C a)
  CopyI :: c a b   -> AddInit c (C a) (C b)

-- | `AddInit c` takes an existing category `c` and adds one object that has one arrow to all the other objects.
instance Category c => Category (AddInit c) where

  src InitO = InitO
  src (InitC _) = InitO
  src (CopyI a) = CopyI (src a)
  
  tgt InitO = InitO
  tgt (InitC a) = CopyI a
  tgt (CopyI a) = CopyI (tgt a)
  
  a . InitO = a
  CopyI a . InitC _ = InitC (tgt a)
  CopyI a . CopyI b = CopyI (a . b)

instance Category c => HasInitialObject (AddInit c) where
  type InitialObject (AddInit c) = I
  initialObject = InitO
  initialize InitO = InitO
  initialize (CopyI a) = InitC a

type instance BinaryProduct (AddInit c) I n = I
type instance BinaryProduct (AddInit c) n I = I
type instance BinaryProduct (AddInit c) (C a) (C b) = C (BinaryProduct c a b)

instance HasBinaryProducts c => HasBinaryProducts (AddInit c) where
  proj1 InitO InitO = InitO
  proj1 InitO (CopyI _) = InitO
  proj1 (CopyI a) InitO = InitC a
  proj1 (CopyI a) (CopyI b) = CopyI (proj1 a b)
  
  proj2 InitO InitO = InitO
  proj2 InitO (CopyI a) = InitC a
  proj2 (CopyI _) InitO = InitO
  proj2 (CopyI a) (CopyI b) = CopyI (proj2 a b)
  
  InitO &&& _ = InitO
  _ &&& InitO = InitO
  InitC a &&& InitC b = InitC (a *** b)
  CopyI a &&& CopyI b = CopyI (a &&& b)

type instance BinaryCoproduct (AddInit c) I n = n
type instance BinaryCoproduct (AddInit c) n I = n
type instance BinaryCoproduct (AddInit c) (C a) (C b) = C (BinaryCoproduct c a b)

instance HasBinaryCoproducts c => HasBinaryCoproducts (AddInit c) where
  inj1 InitO InitO = InitO
  inj1 InitO (CopyI a) = InitC a
  inj1 (CopyI a) InitO = CopyI a
  inj1 (CopyI a) (CopyI b) = CopyI (inj1 a b)

  inj2 InitO InitO = InitO
  inj2 InitO (CopyI a) = CopyI a
  inj2 (CopyI a) InitO = InitC a
  inj2 (CopyI a) (CopyI b) = CopyI (inj2 a b)

  InitO ||| InitO = InitO
  InitC _ ||| b = b
  a ||| InitC _ = a
  CopyI a ||| CopyI b = CopyI (a ||| b)


data AddTerm c a b where
  TermO ::            AddTerm c  T     T
  TermC :: Obj c a -> AddTerm c (C a)  T
  CopyT :: c a b   -> AddTerm c (C a) (C b)

instance Category c => Category (AddTerm c) where
  
  src TermO = TermO
  src (TermC a) = CopyT a
  src (CopyT a) = CopyT (src a)
  
  tgt TermO = TermO
  tgt (TermC _) = TermO
  tgt (CopyT a) = CopyT (tgt a)
  
  TermO . a = a
  TermC _ . CopyT a = TermC (src a)
  CopyT a . CopyT b = CopyT (a . b)

instance Category c => HasTerminalObject (AddTerm c) where
  type TerminalObject (AddTerm c) = T
  terminalObject = TermO
  terminate TermO = TermO
  terminate (CopyT a) = TermC a

type instance BinaryProduct (AddTerm c) T n = n
type instance BinaryProduct (AddTerm c) n T = n
type instance BinaryProduct (AddTerm c) (C a) (C b) = C (BinaryProduct c a b)

instance HasBinaryProducts c => HasBinaryProducts (AddTerm c) where
  proj1 TermO TermO = TermO
  proj1 TermO (CopyT a) = TermC a
  proj1 (CopyT a) TermO = CopyT a
  proj1 (CopyT a) (CopyT b) = CopyT (proj1 a b)
  
  proj2 TermO TermO = TermO
  proj2 TermO (CopyT a) = CopyT a
  proj2 (CopyT a) TermO = TermC a
  proj2 (CopyT a) (CopyT b) = CopyT (proj2 a b)
  
  TermO &&& TermO = TermO
  TermC _ &&& b = b
  a &&& TermC _ = a
  CopyT a &&& CopyT b = CopyT (a &&& b)

type instance BinaryCoproduct (AddTerm c) T n = T
type instance BinaryCoproduct (AddTerm c) n T = T
type instance BinaryCoproduct (AddTerm c) (C a) (C b) = C (BinaryCoproduct c a b)

instance HasBinaryCoproducts c => HasBinaryCoproducts (AddTerm c) where
  inj1 TermO TermO = TermO
  inj1 TermO (CopyT _) = TermO
  inj1 (CopyT a) TermO = TermC a
  inj1 (CopyT a) (CopyT b) = CopyT (inj1 a b)
  
  inj2 TermO TermO = TermO
  inj2 TermO (CopyT a) = TermC a
  inj2 (CopyT _) TermO = TermO
  inj2 (CopyT a) (CopyT b) = CopyT (inj2 a b)
  
  TermO ||| _ = TermO
  _ ||| TermO = TermO
  TermC a ||| TermC b = TermC (a +++ b)
  CopyT a ||| CopyT b = CopyT (a ||| b)


data AddNull c a b where
  NullO ::                       AddNull c  N     N
  InitN :: Obj c a            -> AddNull c  N    (C a)
  TermN :: Obj c a            -> AddNull c (C a)  N
  ZeroN :: Obj c a -> Obj c b -> AddNull c (C a) (C b)
  CopyN :: c a b              -> AddNull c (C a) (C b)

instance Category c => Category (AddNull c) where
  
  src NullO = NullO
  src (InitN _) = NullO
  src (TermN a) = CopyN a
  src (ZeroN a _) = CopyN a
  src (CopyN a) = CopyN (src a)
  
  tgt NullO = NullO
  tgt (InitN a) = CopyN a
  tgt (TermN _) = NullO
  tgt (ZeroN _ b) = CopyN b
  tgt (CopyN a) = CopyN (tgt a)
  
  NullO . a = a
  a . NullO = a

  InitN a . TermN b = ZeroN b a

  TermN _ . InitN _ = NullO

  ZeroN _ a . InitN _ = InitN a
  TermN _ . ZeroN a _ = TermN a

  CopyN a . InitN _ = InitN (tgt a)
  TermN _ . CopyN a = TermN (src a)

  ZeroN _ c . CopyN ab = ZeroN (src ab) c
  CopyN bc . ZeroN a _ = ZeroN a (tgt bc)

  ZeroN _ c . ZeroN a _ = ZeroN a c
  
  CopyN a . CopyN b = CopyN (a . b)
  
instance Category c => HasInitialObject (AddNull c) where
  type InitialObject (AddNull c) = N
  initialObject = NullO
  initialize NullO = NullO
  initialize (CopyN obj) = InitN obj

instance Category c => HasTerminalObject (AddNull c) where
  type TerminalObject (AddNull c) = N
  terminalObject = NullO
  terminate NullO = NullO
  terminate (CopyN obj) = TermN obj


newtype Fix f a b = Fix (f (Fix f) a b)

instance Category (f (Fix f)) => Category (Fix f) where
  src (Fix a) = Fix (src a)
  tgt (Fix a) = Fix (tgt a)
  Fix a . Fix b = Fix (a . b)

instance HasInitialObject (f (Fix f)) => HasInitialObject (Fix f) where
  type InitialObject (Fix f) = InitialObject (f (Fix f))
  initialObject = Fix initialObject
  initialize (Fix o) = Fix (initialize o)

instance HasTerminalObject (f (Fix f)) => HasTerminalObject (Fix f) where
  type TerminalObject (Fix f) = TerminalObject (f (Fix f))
  terminalObject = Fix terminalObject
  terminate (Fix o) = Fix (terminate o)

type instance BinaryProduct (Fix f) a b = BinaryProduct (f (Fix f)) a b
instance HasBinaryProducts (f (Fix f)) => HasBinaryProducts (Fix f) where
  proj1 (Fix a) (Fix b) = Fix (proj1 a b)
  proj2 (Fix a) (Fix b) = Fix (proj2 a b)
  Fix a &&& Fix b = Fix (a &&& b)
  
type instance BinaryCoproduct (Fix f) a b = BinaryCoproduct (f (Fix f)) a b
instance HasBinaryCoproducts (f (Fix f)) => HasBinaryCoproducts (Fix f) where
  inj1 (Fix a) (Fix b) = Fix (inj1 a b)
  inj2 (Fix a) (Fix b) = Fix (inj2 a b)
  Fix a ||| Fix b = Fix (a ||| b)

type Omega = Fix AddInit

