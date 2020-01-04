{-# OPTIONS --cubical --safe #-}

module Data.Bool.Literals where

open import Literals.Number
open import Data.Bool
import Data.Nat as ℕ
import Data.Nat.Order as ℕ
open import Relation.Nullary

instance
  numberBool : Number Bool
  numberBool = record
    { Constraint =  λ n → n ℕ.≤ ℕ.suc ℕ.zero
    ; fromNat = λ { ℕ.zero → false ; (ℕ.suc ℕ.zero) → true}
    }
