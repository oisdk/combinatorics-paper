{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
import Agda.Builtin.Nat as Nat
open import Prelude
open import Cubical.Data.Nat using (caseNat; znots; snotz; injSuc) public

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

correct-== : ∀ n m → Reflects (n ≡ m) (n Nat.== m)
correct-== zero zero = ofʸ refl
correct-== zero (suc m) = ofⁿ znots
correct-== (suc n) zero = ofⁿ snotz
correct-== (suc n) (suc m) =
  map-reflects (cong suc) (λ contra prf  → contra (cong pred prf)) (correct-== n m)

discreteℕ : Discrete ℕ
discreteℕ n m .does = n Nat.== m
discreteℕ n m .why  = correct-== n m

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ
