{-# OPTIONS --cubical --safe #-}

module Data.Rational.Frac where

open import Prelude
import Data.Nat as ℕ
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_; -_)

infixl 7 _÷suc_
record Frac : Type₀ where
  constructor _÷suc_
  field
    num : ℤ
    den-1 : ℕ
open Frac public

infixl 7 _*_
_*_ : Frac → Frac → Frac
(xⁿ ÷suc xᵈ) * (yⁿ ÷suc yᵈ) = (xⁿ ℤ.* yⁿ) ÷suc (xᵈ ℕ.+ yᵈ ℕ.+ xᵈ ℕ.* yᵈ)

infixl 6 _+_
_+_ : Frac → Frac → Frac
(xⁿ ÷suc xᵈ) + (yⁿ ÷suc yᵈ) = (xⁿ ℤ.* + suc yᵈ ℤ.+ yⁿ ℤ.* + suc xᵈ) ÷suc (xᵈ ℕ.+ yᵈ ℕ.+ xᵈ ℕ.* yᵈ)
