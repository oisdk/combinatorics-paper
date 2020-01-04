{-# OPTIONS --cubical --safe #-}

module Induction.WellFounded where

open import Prelude

data Acc {a r} {A : Type a} (R : A → A → Type r) (x : A) : Type (a ℓ⊔ r) where
  acc : (∀ y → R y x → Acc R y) → Acc R x

data _≤_ (m : ℕ) : ℕ → Type₀ where
  m≤m : m ≤ m
  s≤s : ∀ {n} → m ≤ n → m ≤ suc n

_<_ : ℕ → ℕ → Type₀
n < m = suc n ≤ m

mutual
  <-wellFounded : ∀ n → Acc _<_ n
  <-wellFounded n = acc (<-wellFounded′ n)

  <-wellFounded′ : ∀ n m → m < n → Acc _<_ m
  <-wellFounded′ (suc n) .n m≤m = <-wellFounded n
  <-wellFounded′ (suc n) m (s≤s n<m) = <-wellFounded′ n m n<m
