{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
module Language.PlutusTx.IsData.Class where

import           Data.ByteString.Lazy as BSL

import Prelude (Integer, Maybe (..))

import Language.PlutusTx.Data

import Language.PlutusTx.Functor
import Language.PlutusTx.Applicative

import Data.Kind

{-# ANN module "HLint: ignore" #-}

-- | A typeclass for types that can be converted to and from 'Data'.
class IsData (a :: Type) where
    toData :: a -> Data
    -- TODO: this should probably provide some kind of diagnostics
    fromData :: Data -> Maybe a

instance IsData Integer where
    {-# INLINABLE toData #-}
    toData = I
    {-# INLINABLE fromData #-}
    fromData (I i) = Just i
    fromData _     = Nothing

instance IsData ByteString where
    {-# INLINABLE toData #-}
    toData = B
    {-# INLINABLE fromData #-}
    fromData (B b) = Just b
    fromData _     = Nothing

instance IsData a => IsData [a] where
    {-# INLINABLE toData #-}
    toData xs = List (fmap toData xs)
    {-# INLINABLE fromData #-}
    fromData (List ds) = sequence (fmap fromData ds)
    fromData _        = Nothing
