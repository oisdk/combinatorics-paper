{-# OPTIONS --safe --without-K #-}

module Level where

open import Agda.Primitive
  using (Level)
  renaming ( _⊔_ to _ℓ⊔_
           ; lzero to ℓ-zero
           ; lsuc  to ℓ-suc )
  public

Type : (ℓ : Level) → Set (ℓ-suc ℓ)
Type ℓ = Set ℓ

Type₀ = Type ℓ-zero
Type₁ = Type (ℓ-suc ℓ-zero)
Type₂ = Type (ℓ-suc (ℓ-suc ℓ-zero))
Type₃ = Type (ℓ-suc (ℓ-suc (ℓ-suc ℓ-zero)))

variable
  a b c : Level
  A : Type a
  B : Type b
  C : Type c

