\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Binary.Zeroless where

open import Prelude hiding (Bool; true; false)
open import Data.List.Kleene.AsList as List using (List; _∷_; []; foldr)
open import Data.List.Kleene using (_⁺; ∹_; _&_)
open import Data.Bool as Bool
  using (bool′)
  renaming (Bool to Bit; true to 2ᵇ; false to 1ᵇ)
  public
import Data.Nat as ℕ

𝔹 : Type₀
𝔹 = List Bit

𝔹⁺ : Type₀
𝔹⁺ = Bit ⁺

mutual
  inc⁺ : 𝔹 → 𝔹⁺
  inc⁺ []        = 1ᵇ & []
  inc⁺ (1ᵇ ∷ xs) = 2ᵇ & xs
  inc⁺ (2ᵇ ∷ xs) = 1ᵇ & inc xs

  inc : 𝔹 → 𝔹
  inc xs = ∹ inc⁺ xs

dec : 𝔹⁺ → 𝔹
dec (2ᵇ & xs) = 1ᵇ ∷ xs
dec (1ᵇ & []) = []
dec (1ᵇ & ∹ xs) = 2ᵇ ∷ dec xs

dec′ : 𝔹 → 𝔹
dec′ [] = []
dec′ (∹ xs) = dec xs

inc∘dec : ∀ ns → inc⁺ (dec ns) ≡ ns
inc∘dec (2ᵇ & ns) = refl
inc∘dec (1ᵇ & []) = refl
inc∘dec (1ᵇ & ∹ xs) = cong (λ ys → 1ᵇ & ∹ ys) (inc∘dec xs)

dec∘inc : ∀ ns → dec (inc⁺ ns) ≡ ns
dec∘inc [] = refl
dec∘inc (1ᵇ ∷ xs) = refl
dec∘inc (2ᵇ ∷ xs) = cong (2ᵇ ∷_) (dec∘inc xs)

-- Same as:
-- 2* zero = zero
-- 2* (suc n) = suc (suc (2* n))
2* : ℕ → ℕ
2* = ℕ._* 2

_∷⇓_ : Bit → ℕ → ℕ
x ∷⇓ xs = suc (bool′ id suc x (2* xs))

⟦_⇓⟧ : 𝔹 → ℕ
⟦_⇓⟧ = foldr _∷⇓_ zero

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = []
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

2*⇔1ᵇ∷ : ∀ n → inc ⟦ 2* n ⇑⟧ ≡ 1ᵇ ∷ ⟦ n ⇑⟧
2*⇔1ᵇ∷ zero    = refl
2*⇔1ᵇ∷ (suc n) = cong (inc ∘ inc) (2*⇔1ᵇ∷ n)

𝔹→ℕ→𝔹 : ∀ n → ⟦ ⟦ n ⇓⟧ ⇑⟧ ≡ n
𝔹→ℕ→𝔹 [] = refl
𝔹→ℕ→𝔹 (1ᵇ ∷ xs) =           2*⇔1ᵇ∷ ⟦ xs ⇓⟧  ; cong (1ᵇ ∷_) (𝔹→ℕ→𝔹 xs)
𝔹→ℕ→𝔹 (2ᵇ ∷ xs) = cong inc (2*⇔1ᵇ∷ ⟦ xs ⇓⟧) ; cong (2ᵇ ∷_) (𝔹→ℕ→𝔹 xs)

inc⇔suc : ∀ n → ⟦ inc n ⇓⟧ ≡ suc ⟦ n ⇓⟧
inc⇔suc [] = refl
inc⇔suc (1ᵇ ∷ xs) = refl
inc⇔suc (2ᵇ ∷ xs) = cong (suc ∘ 2*) (inc⇔suc xs)

ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ zero = refl
ℕ→𝔹→ℕ (suc n) = inc⇔suc ⟦ n ⇑⟧ ; cong suc (ℕ→𝔹→ℕ n)

𝔹⇔ℕ : 𝔹 ⇔ ℕ
𝔹⇔ℕ = iso ⟦_⇓⟧ ⟦_⇑⟧ ℕ→𝔹→ℕ 𝔹→ℕ→𝔹

infixl 6 _+_ _+₁_ _+₂_

_+₁_ _+₂_ : 𝔹 → 𝔹 → 𝔹⁺

[]        +₁ ys        = inc⁺ ys
(∹ xs)    +₁ []        = inc⁺ (∹ xs)
(1ᵇ ∷ xs) +₁ (1ᵇ ∷ ys) = 1ᵇ & ∹ xs +₁ ys
(1ᵇ ∷ xs) +₁ (2ᵇ ∷ ys) = 2ᵇ & ∹ xs +₁ ys
(2ᵇ ∷ xs) +₁ (1ᵇ ∷ ys) = 2ᵇ & ∹ xs +₁ ys
(2ᵇ ∷ xs) +₁ (2ᵇ ∷ ys) = 1ᵇ & ∹ xs +₂ ys

[]        +₂ []        = 2ᵇ & []
[]        +₂ (y  ∷ ys) = y & inc ys
(x  ∷ xs) +₂ []        = x & inc xs
(1ᵇ ∷ xs) +₂ (1ᵇ ∷ ys) = 2ᵇ & ∹ xs +₁ ys
(1ᵇ ∷ xs) +₂ (2ᵇ ∷ ys) = 1ᵇ & ∹ xs +₂ ys
(2ᵇ ∷ xs) +₂ (1ᵇ ∷ ys) = 1ᵇ & ∹ xs +₂ ys
(2ᵇ ∷ xs) +₂ (2ᵇ ∷ ys) = 2ᵇ & ∹ xs +₂ ys

_+_ : 𝔹 → 𝔹 → 𝔹
[]        + ys        = ys
(∹ xs)    + []        = ∹ xs
(1ᵇ ∷ xs) + (1ᵇ ∷ ys) = 2ᵇ ∷   xs +  ys
(1ᵇ ∷ xs) + (2ᵇ ∷ ys) = 1ᵇ ∷ ∹ xs +₁ ys
(2ᵇ ∷ xs) + (1ᵇ ∷ ys) = 1ᵇ ∷ ∹ xs +₁ ys
(2ᵇ ∷ xs) + (2ᵇ ∷ ys) = 2ᵇ ∷ ∹ xs +₁ ys
\end{code}
