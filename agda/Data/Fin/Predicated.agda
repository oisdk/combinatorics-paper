{-# OPTIONS --cubical --safe #-}

module Data.Fin.Predicated where

open import Prelude

open import Data.Nat
open import Data.Nat.Order

private variable n m : ℕ

Fin : ℕ → Type₀
Fin n = ∃ (_< n)

fs : Fin n → Fin (suc n)
fs (n , p) = suc n , p

pattern f0 = zero , tt

