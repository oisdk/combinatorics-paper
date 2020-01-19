{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Categories
open import Categories.Functor

module Categories.Cone
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {C : Category ℓ₁ ℓ₂}
  {J : Category ℓ₃ ℓ₄}
  (F : Functor (Category.preCategory J) (Category.preCategory C))
  where

open Category C
open Functor F

record Apex (N : Ob) : Type (ℓ₂ ℓ⊔ ℓ₃ ℓ⊔ ℓ₄) where
  field
    ψ : (X : Category.Ob J) → (N ⟶ F₀ X)
    commute : ∀ {X Y} → (f : J [ X , Y ]) → F₁ f · ψ X ≡ ψ Y

record Cone : Type (ℓ₁ ℓ⊔ ℓ₂ ℓ⊔ ℓ₃ ℓ⊔ ℓ₄) where
  field
    {N} : Ob
    apex : Apex N
