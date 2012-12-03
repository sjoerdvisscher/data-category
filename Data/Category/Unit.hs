{-# LANGUAGE GADTs, NoImplicitPrelude #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Category.Unit
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Category.Unit where

import Data.Category


data Unit a b where
  Unit :: Unit () ()

-- | `Unit` is the category with one object.
instance Category Unit where

  src Unit = Unit
  tgt Unit = Unit

  Unit . Unit = Unit
