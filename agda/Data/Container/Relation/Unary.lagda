\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Data.Container

module Data.Container.Relation.Unary {s p} (𝒞 : Container s p) where

open import Prelude

◻ : ∀ {x ℓ} {X : Type x} (P : X → Type ℓ) (cx : ⟦ 𝒞 ⟧ X) → Type (p ℓ⊔ ℓ)
◻ P cx = ∀ p → P (snd cx p)

◇ : ∀ {x ℓ} {X : Type x} (P : X → Type ℓ) (cx : ⟦ 𝒞 ⟧ X) → Type (p ℓ⊔ ℓ)
◇ P cx = ∃[ p ] (P (snd cx p))

◇! : ∀ {x ℓ} {X : Type x} (P : X → Type ℓ) (cx : ⟦ 𝒞 ⟧ X) → Type (p ℓ⊔ ℓ)
◇! P cx = isContr (◇ P cx)

◻⇒¬◇¬ : ∀ {x ℓ} {X : Type x} (P : X → Type ℓ) {cx : ⟦ 𝒞 ⟧ X}
      → ◻ P cx → ¬ ◇ (¬_ ∘ P) cx
◻⇒¬◇¬ P ◻Pxs (n , ◇¬Pxs) = ◇¬Pxs (◻Pxs n)

◇⇒¬◻¬ : ∀ {x ℓ} {X : Type x} (P : X → Type ℓ) {cx : ⟦ 𝒞 ⟧ X}
      → ◇ P cx → ¬ ◻ (¬_ ∘ P) cx
◇⇒¬◻¬ P (n , ◇Pxs) ◻¬Pxs = ◻¬Pxs n ◇Pxs

infixr 5 _∈_ _∉_ _∈!_
_∈_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∈ xs = ◇ (_≡ x) xs

_∉_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∉ xs = ¬ (x ∈ xs)

_∈!_ : A → ⟦ 𝒞 ⟧ A → Type _
x ∈! xs = ◇! (_≡ x) xs

module Congruence {p q} (P : A → Type p) (Q : B → Type q)
                  {f : A → B} (f↑ : ∀ {x} → P x → Q (f x)) where
  cong-◇ : ∀ {xs} → ◇ P xs → ◇ Q (map f xs)
  cong-◇ = map₂ f↑
\end{code}
