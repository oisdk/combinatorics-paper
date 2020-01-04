\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.Construct.Free.Semimodule.Direct.Definition {s} (rng : Semiring s) where

open import Prelude

open Semiring rng

infixl 6 _∪_
infixr 7 _⋊_
data 𝒱 (A : Type a) : Type (s ℓ⊔ a) where
  [_] : A → 𝒱 A
  _⋊_ : 𝑅 → 𝒱 A → 𝒱 A

  _∪_ : 𝒱 A → 𝒱 A → 𝒱 A
  ∅ : 𝒱 A


  ∪-com : ∀ xs ys → xs ∪ ys ≡ ys ∪ xs
  ∪-assoc : ∀ xs ys zs → (xs ∪ ys) ∪ zs ≡ xs ∪ (ys ∪ zs)
  ∅∪ : ∀ xs → ∅ ∪ xs ≡ xs

  ⟨*⟩⋊ : ∀ x y z → (x * y) ⋊ z ≡ x ⋊ (y ⋊ z)
  ⟨+⟩⋊ : ∀ x y z → (x + y) ⋊ z ≡ (x ⋊ z) ∪ (y ⋊ z)
  ⋊⟨∪⟩ : _⋊_ Distributesʳ _∪_
  1⋊ : Identityˡ _⋊_ 1#
  0⋊ : ∀ xs → 0# ⋊ xs ≡ ∅

  trunc : isSet (𝒱 A)
\end{code}
