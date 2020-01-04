{-# OPTIONS --cubical --safe #-}

module Data.Fin.Literals where

import Data.Nat as ℕ
import Data.Nat.Order as ℕ
open import Data.Fin
open import Literals.Number
open import Relation.Nullary

instance
  numberFin : ∀ {n} → Number (Fin n)
  numberFin {n} = record
    { Constraint = λ m → m ℕ.< n
    ; fromNat    = λ m {{pr}} → ℕToFin m pr
    }
