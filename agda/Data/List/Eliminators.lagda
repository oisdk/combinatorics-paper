\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.List.Eliminators where

open import Prelude
open import Data.List
open import Algebra

open _↘_ public
open _⇘_ public

module _ {b} {B : Type b} {r} {R : B → B → Type r} where
  infix 4 _≈_
  private _≈_ = R
  open import Relation.Binary

  record _≈[_]↓ {a} {A : Type a} (h : List A → B) (f : A ↘ B) : Type (a ℓ⊔ b ℓ⊔ r) where
    constructor univ
    field
      ⟦_≈⟧_∷_ : ∀ x xs → h (x ∷ xs) ≈ [ f ] x ∷ h xs
      ⟦_≈⟧[] : h [] ≈ [ f ][]
      ⟦_≈⟧-cong : ∀ {x xs ys} → xs ≈ ys → [ f ] x ∷ xs ≈ [ f ] x ∷ ys
      ⟦_≈⟧-trans : Transitive _≈_

    ⟦_≈⟧⇓ : ∀ xs → h xs ≈ [ f ]↓ xs
    ⟦_≈⟧⇓ = ⟦ proof ⟧⇓
      where
      proof : xs ⦂List A ⇘ h xs ≈ [ f ]↓ xs
      ⟦ proof ⟧[] = ⟦_≈⟧[]
      ⟦ proof ⟧ x ∷ xs ⟨ P ⟩ = ⟦_≈⟧-trans (⟦_≈⟧_∷_ x xs) (⟦_≈⟧-cong P)
  open _≈[_]↓ public

  record _∘[_]↓≈[_]↓ {a c} {A : Type a} {C : Type c} (h : C → B) (f : A ↘ C) (g : A ↘ B)
      : Type (a ℓ⊔ b ℓ⊔ c ℓ⊔ r) where
    constructor fuse
    field
      ⟦_∘≈⟧_∷_ : ∀ x xs → h ([ f ] x ∷ xs) ≈ [ g ] x ∷ h xs
      ⟦_∘≈⟧[] : h [ f ][] ≈ [ g ][]
      ⟦_∘≈⟧-trans : Transitive _≈_
      ⟦_∘≈⟧-cong : ∀ {x xs ys} → xs ≈ ys → [ g ] x ∷ xs ≈ [ g ] x ∷ ys
    ⟦_∘≈⟧⇓ : ∀ xs → h ([ f ]↓ xs) ≈ [ g ]↓ xs
    ⟦_∘≈⟧⇓ = ⟦ univ (λ x xs → ⟦_∘≈⟧_∷_ x ([ f ]↓ xs)) ⟦_∘≈⟧[] ⟦_∘≈⟧-cong ⟦_∘≈⟧-trans ≈⟧⇓
  open _∘[_]↓≈[_]↓ public

record _≡[_]↓ {a b} {A : Type a} {B : Type b} (h : List A → B) (f : A ↘ B) : Type (a ℓ⊔ b) where
  constructor univ-≡
  field
    ⟦_≡⟧_∷_ : ∀ x xs → h (x ∷ xs) ≡ [ f ] x ∷ h xs
    ⟦_≡⟧[] : h [] ≡ [ f ][]

  ⟦_≡⟧⇓ : h ≡ [ f ]↓
  ⟦_≡⟧⇓ = funExt ⟦ univ {R = _≡_} ⟦_≡⟧_∷_ ⟦_≡⟧[] (λ {x} → cong ([ f ] x ∷_)) _;_ ≈⟧⇓
open _≡[_]↓ public

record _∘[_]↓≡[_]↓ {a b c} {A : Type a} {B : Type b} {C : Type c} (h : C → B) (f : A ↘ C) (g : A ↘ B)
      : Type (a ℓ⊔ b ℓ⊔ c) where
  constructor fuse-≡
  field
    ⟦_∘≡⟧_∷_ : ∀ x xs → h ([ f ] x ∷ xs) ≡ [ g ] x ∷ h xs
    ⟦_∘≡⟧[] : h [ f ][] ≡ [ g ][]
  ⟦_∘≡⟧⇓ : h ∘ [ f ]↓ ≡ [ g ]↓
  ⟦_∘≡⟧⇓ = ⟦ univ-≡ (λ x xs → ⟦_∘≡⟧_∷_ x ([ f ]↓ xs)) ⟦_∘≡⟧[] ≡⟧⇓
open _∘[_]↓≡[_]↓ public
\end{code}
