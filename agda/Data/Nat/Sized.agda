{-# OPTIONS --cubical --safe --sized-types #-}

module Data.Nat.Sized where

open import Prelude
open import Codata.Size

data Szℕ : Size → Type₀ where
  zero : Szℕ i
  suc : Szℕ i → Szℕ (↑ i)

ℕToSize : ℕ → Size
ℕToSize zero = ∞
ℕToSize (suc n) = ↑ (ℕToSize n)

fromℕ : ℕ → Szℕ ∞
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

fromℕSz : (n : ℕ) → Szℕ (ℕToSize n)
fromℕSz zero = zero
fromℕSz (suc n) = suc {i = ℕToSize n} (fromℕSz n)

toℕ : Szℕ i → ℕ
toℕ zero = zero
toℕ (suc n) = suc (toℕ n)

ℕ→Szℕ→ℕ : ∀ n → toℕ (fromℕ n) ≡ n
ℕ→Szℕ→ℕ zero = refl
ℕ→Szℕ→ℕ (suc n) = cong suc (ℕ→Szℕ→ℕ n)

Szℕ→ℕ→Szℕ : ∀ n → fromℕ (toℕ n) ≡ n
Szℕ→ℕ→Szℕ zero = refl
Szℕ→ℕ→Szℕ (suc n) = cong suc (Szℕ→ℕ→Szℕ n)

ℕ⇔Szℕ : ℕ ⇔ Szℕ ∞
ℕ⇔Szℕ .fun = fromℕ
ℕ⇔Szℕ .inv = toℕ
ℕ⇔Szℕ .rightInv = Szℕ→ℕ→Szℕ
ℕ⇔Szℕ .leftInv = ℕ→Szℕ→ℕ
