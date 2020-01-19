{-# OPTIONS --cubical --safe #-}

open import Prelude
open import Categories

module Categories.Pullback {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) where

open Category C

record Pullback (f : X ⟶ Z) (g : Y ⟶ Z) : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field
    {P} : Ob
    p₁ : P ⟶ X
    p₂ : P ⟶ Y
    commute : f · p₁ ≡ g · p₂
    universal : ∀ {A : Ob} {h₁ : A ⟶ X} {h₂ : A ⟶ Y} → f · h₁ ≡ g · h₂ → A ⟶ P
    unique : ∀ {A : Ob} {h₁ : A ⟶ X} {h₂ : A ⟶ Y} {eq : f · h₁ ≡ g · h₂} →
             {i : A ⟶ P} →
             p₁ · i ≡ h₁ → p₂ · i ≡ h₂ →
             i ≡ universal eq

    p₁·universal≡h₁  : ∀ {A : Ob} {h₁ : A ⟶ X} {h₂ : A ⟶ Y} {eq : f · h₁ ≡ g · h₂} →
                         p₁ · universal eq ≡ h₁
    p₂·universal≡h₂  : ∀ {A : Ob} {h₁ : A ⟶ X} {h₂ : A ⟶ Y} {eq : f · h₁ ≡ g · h₂} →
                         p₂ · universal eq ≡ h₂

record HasPullbacks : Type (ℓ₁ ℓ⊔ ℓ₂) where
  field pullback : ∀ {X Y Z} (f : X ⟶ Z) (g : Y ⟶ Z) → Pullback f g
