{-# LANGUAGE TypeFamilies, GADTs, PolyKinds, DataKinds, FlexibleInstances, FlexibleContexts, UndecidableInstances, NoImplicitPrelude #-}
{-# LANGUAGE EmptyCase, TypeApplications, ScopedTypeVariables #-}
module Data.Category.Fin where

import Data.Category
import Data.Category.Limit
import Data.Category.CartesianClosed

data Nat = Z | S Nat

data Fin n where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

data LTE (n :: Nat) (a :: Fin n) (b :: Fin n) where
  ZEQ :: LTE ('S m) 'FZ 'FZ
  ZLT :: LTE ('S m) 'FZ  b -> LTE ('S ('S m))  'FZ    ('FS b)
  SLT :: LTE ('S m)  a   b -> LTE ('S ('S m)) ('FS a) ('FS b)

instance Category (LTE n) where
  src ZEQ = ZEQ
  src (ZLT _) = ZEQ
  src (SLT a) = SLT (src a)
  tgt ZEQ = ZEQ
  tgt (ZLT a) = SLT (tgt a)
  tgt (SLT a) = SLT (tgt a)
  ZEQ . a = a
  a . ZEQ = a
  SLT a . ZLT b = ZLT (a . b)
  SLT a . SLT b = SLT (a . b)

instance HasInitialObject (LTE ('S n)) where
  type InitialObject (LTE ('S n)) = 'FZ
  initialObject = ZEQ
  initialize ZEQ = ZEQ
  initialize (SLT a) = ZLT (initialize a)

instance HasTerminalObject (LTE ('S 'Z)) where
  type TerminalObject (LTE ('S 'Z)) = 'FZ
  terminalObject = ZEQ
  terminate ZEQ = ZEQ

instance HasTerminalObject (LTE ('S n)) => HasTerminalObject (LTE ('S ('S n))) where
  type TerminalObject (LTE ('S ('S n))) = 'FS (TerminalObject (LTE ('S n)))
  terminalObject = SLT terminalObject
  terminate ZEQ = ZLT (terminate ZEQ)
  terminate (SLT a) = SLT (terminate a)

instance HasBinaryCoproducts (LTE ('S 'Z)) where
  type BinaryCoproduct (LTE ('S 'Z)) 'FZ 'FZ = 'FZ
  inj1 ZEQ ZEQ = ZEQ
  inj2 ZEQ ZEQ = ZEQ
  ZEQ ||| ZEQ = ZEQ

instance HasBinaryCoproducts (LTE ('S n)) => HasBinaryCoproducts (LTE ('S ('S n))) where
  type BinaryCoproduct (LTE ('S ('S n))) 'FZ 'FZ = 'FZ
  type BinaryCoproduct (LTE ('S ('S n))) 'FZ ('FS b) = 'FS (BinaryCoproduct (LTE ('S n)) 'FZ b)
  type BinaryCoproduct (LTE ('S ('S n))) ('FS a) 'FZ = 'FS (BinaryCoproduct (LTE ('S n)) a 'FZ)
  type BinaryCoproduct (LTE ('S ('S n))) ('FS a) ('FS b) = 'FS (BinaryCoproduct (LTE ('S n)) a b)
  inj1 ZEQ ZEQ = ZEQ
  inj1 ZEQ (SLT a) = ZLT (inj1 ZEQ a)
  inj1 (SLT a) ZEQ = SLT (inj1 a ZEQ)
  inj1 (SLT a) (SLT b) = SLT (inj1 a b)
  inj2 ZEQ ZEQ = ZEQ
  inj2 ZEQ (SLT a) = SLT (inj2 ZEQ a)
  inj2 (SLT a) ZEQ = ZLT (inj2 a ZEQ)
  inj2 (SLT a) (SLT b) = SLT (inj2 a b)
  ZEQ ||| ZEQ = ZEQ
  ZLT a ||| ZLT b = ZLT (case a ||| b of { ZEQ -> ZEQ; ZLT n -> ZLT n })
  ZLT a ||| SLT b = SLT (a ||| b)
  SLT a ||| ZLT b = SLT (a ||| b)
  SLT a ||| SLT b = SLT (a ||| b)

instance HasBinaryProducts (LTE ('S 'Z)) where
  type BinaryProduct (LTE ('S 'Z)) 'FZ 'FZ = 'FZ
  proj1 ZEQ ZEQ = ZEQ
  proj2 ZEQ ZEQ = ZEQ
  ZEQ &&& ZEQ = ZEQ

instance HasBinaryProducts (LTE ('S n)) => HasBinaryProducts (LTE ('S ('S n))) where
  type BinaryProduct (LTE ('S ('S n))) 'FZ 'FZ = 'FZ
  type BinaryProduct (LTE ('S ('S n))) 'FZ ('FS b) = 'FZ
  type BinaryProduct (LTE ('S ('S n))) ('FS a) 'FZ = 'FZ
  type BinaryProduct (LTE ('S ('S n))) ('FS a) ('FS b) = 'FS (BinaryProduct (LTE ('S n)) a b)
  proj1 ZEQ ZEQ = ZEQ
  proj1 ZEQ (SLT _) = ZEQ
  proj1 (SLT a) ZEQ = ZLT (case proj1 a ZEQ of { ZEQ -> ZEQ; ZLT n -> ZLT n })
  proj1 (SLT a) (SLT b) = SLT (proj1 a b)
  proj2 ZEQ ZEQ = ZEQ
  proj2 ZEQ (SLT a) = ZLT (case proj2 ZEQ a of { ZEQ -> ZEQ; ZLT n -> ZLT n })
  proj2 (SLT _) ZEQ = ZEQ
  proj2 (SLT a) (SLT b) = SLT (proj2 a b)
  ZEQ &&& ZEQ = ZEQ
  ZEQ &&& ZLT _ = ZEQ
  ZLT _ &&& ZEQ = ZEQ
  ZLT a &&& ZLT b = ZLT (a &&& b)
  SLT a &&& SLT b = SLT (a &&& b)

data Proof a n where
  Proof :: (BinaryProduct (LTE ('S n)) 'FZ a ~ 'FZ, BinaryProduct (LTE ('S n)) a 'FZ ~ 'FZ) => Proof a n
proof :: Obj (LTE ('S n)) a -> Proof a n
proof = proof -- trust me

instance CartesianClosed (LTE ('S 'Z)) where
  type Exponential (LTE ('S 'Z)) 'FZ 'FZ = 'FZ
  apply ZEQ ZEQ = ZEQ
  tuple ZEQ ZEQ = ZEQ
  ZEQ ^^^ ZEQ = ZEQ

-- b -> c = max(a: min(a, b) <= c)
-- → 0 1 2 3
--  +-------
-- 0|3 3 3 3
-- 1|0 3 3 3
-- 2|0 1 3 3
-- 3|0 1 2 3
instance CartesianClosed (LTE ('S n)) => CartesianClosed (LTE ('S ('S n))) where
  type Exponential (LTE ('S ('S n))) 'FZ 'FZ = 'FS (Exponential (LTE ('S n)) 'FZ 'FZ)
  type Exponential (LTE ('S ('S n))) 'FZ ('FS b) = 'FS (Exponential (LTE ('S n)) 'FZ b)
  type Exponential (LTE ('S ('S n))) ('FS a) 'FZ = 'FZ
  type Exponential (LTE ('S ('S n))) ('FS a) ('FS b) = 'FS (Exponential (LTE ('S n)) a b)
  apply ZEQ ZEQ = ZEQ
  apply ZEQ (SLT a) = ZLT (case apply ZEQ a of { ZEQ -> ZEQ; ZLT n -> ZLT n })
  apply (SLT _) ZEQ = ZEQ
  apply (SLT a) (SLT b) = SLT (apply a b)
  tuple ZEQ ZEQ = case proof (ZEQ @n) of Proof -> ZLT (tuple ZEQ ZEQ)
  tuple ZEQ (SLT a) = case proof (src a) of Proof -> SLT (tuple ZEQ a)
  tuple (SLT _) ZEQ = ZEQ
  tuple (SLT a) (SLT b) = SLT (tuple a b)
  ZEQ ^^^ ZEQ = SLT (ZEQ ^^^ ZEQ)
  ZEQ ^^^ ZLT a = ZLT (initialize (tgt (ZEQ ^^^ a)))
  ZEQ ^^^ SLT _ = ZEQ
  ZLT a ^^^ ZEQ = SLT (a ^^^ ZEQ)
  ZLT a ^^^ ZLT b = ZLT (initialize (tgt (a ^^^ b)))
  ZLT a ^^^ SLT b = ZLT (initialize (tgt (a ^^^ b)))
  SLT a ^^^ ZEQ = SLT (a ^^^ ZEQ)
  SLT a ^^^ ZLT b = SLT (a ^^^ b)
  SLT a ^^^ SLT b = SLT (a ^^^ b)

