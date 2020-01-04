{-# OPTIONS --safe --cubical --sized-types #-}

module Codata.Cofin.Literals where

open import Codata.Cofin
open import Literals.Number
open import Codata.Size
open import Relation.Nullary
open import Codata.Conat
import Data.Nat as ℕ

instance
  numberCofin : ∀ {n} → Number (Cofin n)
  numberCofin {n} = record
    { Constraint = λ m → True (ℕ.suc m ℕ≤? n)
    ; fromNat    = λ m {{pr}} → ℕToCofin m (toWitness pr)
    }
