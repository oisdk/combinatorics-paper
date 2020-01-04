{-# OPTIONS --cubical --safe #-}

module Data.Binary.OneTerminated.Properties where

open import Prelude
open import Data.Binary.OneTerminated
open import Data.List

dec∘inc⁺ : ∀ n → dec (inc⁺ n) ≡ just n
dec∘inc⁺ [] = refl
dec∘inc⁺ (O ∷ xs) = refl
dec∘inc⁺ (I ∷ xs) = cong (just ∘ I∷_) (dec∘inc⁺ xs)

inc⁺∘dec′ : ∀ n ns → inc⁺ (Decrement.dec′ n ns) ≡ n ∷ ns
inc⁺∘dec′ O [] = refl
inc⁺∘dec′ O (n ∷ ns) = cong (O ∷_) (inc⁺∘dec′ n ns)
inc⁺∘dec′ I ns = refl

inc∘dec : ∀ n → inc (dec n) ≡ just n
inc∘dec [] = refl
inc∘dec (n ∷ ns) = cong just (inc⁺∘dec′ n ns)

inc⁺⇔suc : ∀ n → ⟦ inc⁺ n ⇓⟧⁺ ≡ suc ⟦ n ⇓⟧⁺
inc⁺⇔suc [] = refl
inc⁺⇔suc (O ∷ xs) = refl
inc⁺⇔suc (I ∷ xs) = cong 2* (inc⁺⇔suc xs)

2*⇔O∷ : ∀ x → ⟦ 2* x ⇑⟧ ≡ O∷ ⟦ x ⇑⟧
2*⇔O∷ zero = refl
2*⇔O∷ (suc zero) = refl
2*⇔O∷ (suc (suc x)) = cong (inc ∘ inc) (2*⇔O∷ (suc x))

ℕ→𝔹⁺→ℕ : ∀ n → ⟦ maybe inc⁺ [] ⟦ n ⇑⟧ ⇓⟧⁺ ≡ suc n
ℕ→𝔹⁺→ℕ zero = refl
ℕ→𝔹⁺→ℕ (suc n) = inc⁺⇔suc (maybe inc⁺ [] ⟦ n ⇑⟧) ; cong suc (ℕ→𝔹⁺→ℕ n)

ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ zero = refl
ℕ→𝔹→ℕ (suc x) = ℕ→𝔹⁺→ℕ x

𝔹⁺→ℕ→𝔹 : ∀ n → ⟦ ⟦ n ⇓⟧⁺ ⇑⟧ ≡ just n
𝔹⁺→ℕ→𝔹 [] = refl
𝔹⁺→ℕ→𝔹 (O ∷ xs) = 2*⇔O∷ ⟦ xs ⇓⟧⁺ ; cong O∷_ (𝔹⁺→ℕ→𝔹 xs)
𝔹⁺→ℕ→𝔹 (I ∷ xs) = cong inc (2*⇔O∷ ⟦ xs ⇓⟧⁺) ; cong (inc ∘ O∷_) (𝔹⁺→ℕ→𝔹 xs)

𝔹→ℕ→𝔹 : ∀ n → ⟦ ⟦ n ⇓⟧ ⇑⟧ ≡ n
𝔹→ℕ→𝔹 nothing = refl
𝔹→ℕ→𝔹 (just xs) = 𝔹⁺→ℕ→𝔹 xs

ℕ⇔𝔹 : ℕ ⇔ 𝔹
ℕ⇔𝔹 = iso ⟦_⇑⟧ ⟦_⇓⟧ 𝔹→ℕ→𝔹 ℕ→𝔹→ℕ
