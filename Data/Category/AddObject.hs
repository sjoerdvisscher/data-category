{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts #-}
import Prelude (error)
import Data.Category

data O
data I
data T
data N
data C n


data AddObject c a b where
  Object :: AddObject c O O
  CopyO :: c a b -> AddObject c (C a) (C b)

instance Category c => Category (AddObject c) where
  
  src Object = Object
  src (CopyO a) = CopyO (src a)
  
  tgt Object = Object
  tgt (CopyO a) = CopyO (tgt a)
  
  Object . Object = Object
  CopyO a . CopyO b = CopyO (a . b)
  _ . _ = error "Other combinations should not type check"
  

data AddInit c a b where
  InitO ::            AddInit c  I     I
  InitC :: Obj c a -> AddInit c  I    (C a)
  CopyI :: c a b   -> AddInit c (C a) (C b)

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
  _ . _ = error "Other combinations should not type check"
  

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
  _ . _ = error "Other combinations should not type check"


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
  
  _ . _ = error "Other combinations should not type check"