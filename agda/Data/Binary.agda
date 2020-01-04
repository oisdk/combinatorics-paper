{-# OPTIONS --safe --cubical #-}

module Data.Binary where

-- There are several different ways to implement binary numbers.
-- This module imports (and reexports) what I think is the best
-- representation, the zeroless binary numbers.

open import Data.Binary.Zeroless public
