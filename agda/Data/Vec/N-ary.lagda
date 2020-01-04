\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Vec.N-ary where

open import Data.Vec
open import Prelude

N-ary-level : Level → Level → ℕ → Level
N-ary-level ℓ₁ ℓ₂ zero    = ℓ₂
N-ary-level ℓ₁ ℓ₂ (suc n) = ℓ₁ ℓ⊔ N-ary-level ℓ₁ ℓ₂ n

_⌈_⌉→_ : Type a → (n : ℕ) → Type b → Type (N-ary-level a b n)
A ⌈ zero  ⌉→ B = B
A ⌈ suc n ⌉→ B = A → A ⌈ n ⌉→ B

curryⁿ : ∀ {n} → (Vec A n → B) → A ⌈ n ⌉→ B
curryⁿ {n = zero}  f = f []
curryⁿ {n = suc n} f = λ x → curryⁿ (f ∘ _∷_ x)

_$ⁿ_ : ∀ {n} → (A ⌈ n ⌉→ B) → (Vec A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

module _ {A : Type a} where
  ∀ⁿ : ∀ {ℓ} n → A ⌈ n ⌉→ Type ℓ → Type (N-ary-level a ℓ n)
  ∀ⁿ zero    P = P
  ∀ⁿ (suc n) P = ∀ x → ∀ⁿ n (P x)

\end{code}
