{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Base where

open import Agda.Builtin.Sigma
  using (Σ; _,_; fst; snd)
  public
open import Level

∃ : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃ {A = A} = Σ A

infixr 3 ∃-syntax
∃-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → e) = ∃[ x ] e

infixr 3 Σ⦂-syntax
Σ⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ⦂-syntax = Σ

syntax Σ⦂-syntax t (λ x → e) = Σ[ x ⦂ t ] e

infixr 4 _×_
_×_ : (A : Type a) → (B : Type b) → Type (a ℓ⊔ b)
A × B = Σ A λ _ → B
