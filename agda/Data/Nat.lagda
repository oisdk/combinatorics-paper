\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Nat where

open import Agda.Builtin.Nat public
  using (_+_; _*_; zero; suc)
  renaming (Nat to ℕ)
open import Cubical.Data.Nat using (caseNat; znots; snotz; injSuc) public
import Agda.Builtin.Nat as Nat
open import Relation.Nullary
open import Path
open import Data.Bool using (Bool; true; false; T; bool; not)
open import Function
open import Data.Unit
open import Level
open import Relation.Nullary
open import HLevels

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

correct-== : ∀ n m → Reflects (n ≡ m) (n Nat.== m)
correct-== zero zero = ofʸ refl
correct-== zero (suc m) = ofⁿ znots
correct-== (suc n) zero = ofⁿ snotz
correct-== (suc n) (suc m) =
  ⟦y cong suc ,n cong pred ⟧ (correct-== n m)

discreteℕ : Discrete ℕ
discreteℕ n m .does = n Nat.== m
discreteℕ n m .why  = correct-== n m

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

data Ordering : ℕ → ℕ → Type₀ where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
... | less    m k = less (suc m) k
... | equal   m   = equal (suc m)
... | greater n k = greater (suc n) k
\end{code}
