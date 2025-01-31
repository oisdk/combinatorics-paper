{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᴮ_; _==_ to _≡ᴮ_) public
open import Prelude
open import Cubical.Data.Nat using (caseNat; znots; snotz; injSuc) public

pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero

correct-== : ∀ n m → Reflects (n ≡ m) (n ≡ᴮ m)
correct-== zero zero = ofʸ refl
correct-== zero (suc m) = ofⁿ znots
correct-== (suc n) zero = ofⁿ snotz
correct-== (suc n) (suc m) =
  map-reflects (cong suc) (λ contra prf  → contra (cong pred prf)) (correct-== n m)

discreteℕ : Discrete ℕ
discreteℕ n m .does = n ≡ᴮ m
discreteℕ n m .why  = correct-== n m

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-idʳ : ∀ x → x + 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ; cong suc (+-comm x y)

infix 4 _<_
_<_ : ℕ → ℕ → Type₀
n < m = T (n <ᴮ m)

_≤ᴮ_ : ℕ → ℕ → Bool
zero  ≤ᴮ m = true
suc n ≤ᴮ m = n <ᴮ m

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)
