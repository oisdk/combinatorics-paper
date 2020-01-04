{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.Construct.Group.Grothendieck {ℓ} (mon : CommutativeMonoid ℓ) where

open import Prelude
open import Path.Reasoning

open CommutativeMonoid mon

data 𝒢 : Type ℓ where
  _⊝_ : (x⁺ x⁻ : 𝑆) → 𝒢
  cancel : ∀ k x⁺ x⁻ y⁺ y⁻ → (diff : x⁺ ∙ y⁻ ∙ k ≡ x⁻ ∙ y⁺ ∙ k) → x⁺ ⊝ x⁻ ≡ y⁺ ⊝ y⁻

invg : 𝒢 → 𝒢
invg (x⁺ ⊝ x⁻) = x⁻ ⊝ x⁺
invg (cancel k x⁺ x⁻ y⁺ y⁻ diff i) = cancel k x⁻ x⁺ y⁻ y⁺ (sym diff) i

-- lemma : ∀ x⁺ x⁻ y⁺ y⁻ z⁺ z⁻ k →
--         y⁺ ∙ z⁻ ∙ k ≡ y⁻ ∙ z⁺ ∙ k →
--         x⁺ ∙ y⁺ ∙ (x⁻ ∙ z⁻) ∙ k ≡ x⁻ ∙ y⁻ ∙ (x⁺ ∙ z⁺) ∙ k
-- lemma x⁺ x⁻ y⁺ y⁻ z⁺ z⁻ k diff =
--   ((x⁺ ∙ y⁺) ∙ (x⁻ ∙ z⁻)) ∙ k ≡⟨ {!!} ⟩
--   (x⁺ ∙ (y⁺ ∙ (x⁻ ∙ z⁻))) ∙ k ≡⟨ {!!} ⟩
--   (x⁺ ∙ ((y⁺ ∙ x⁻) ∙ z⁻)) ∙ k ≡⟨ {!!} ⟩
--   (x⁺ ∙ ((x⁻ ∙ y⁺) ∙ z⁻)) ∙ k ≡⟨ {!!} ⟩
--   (x⁺ ∙ (x⁻ ∙ (y⁺ ∙ z⁻))) ∙ k ≡⟨ {!!} ⟩
--   ((x⁺ ∙ x⁻) ∙ (y⁺ ∙ z⁻)) ∙ k ≡⟨ {!!} ⟩
--   (x⁺ ∙ x⁻) ∙ ((y⁺ ∙ z⁻) ∙ k) ≡⟨ cong (x⁺ ∙ x⁻ ∙_) diff ⟩
--   (x⁺ ∙ x⁻) ∙ ((y⁻ ∙ z⁺) ∙ k) ≡⟨ {!!} ⟩
--   ((x⁺ ∙ x⁻) ∙ (y⁻ ∙ z⁺)) ∙ k ≡⟨ {!!} ⟩
--   ((x⁻ ∙ x⁺) ∙ (y⁻ ∙ z⁺)) ∙ k ≡⟨ {!!} ⟩
--   (((x⁻ ∙ x⁺) ∙ y⁻) ∙ z⁺) ∙ k ≡⟨ {!!} ⟩
--   ((x⁻ ∙ (x⁺ ∙ y⁻)) ∙ z⁺) ∙ k ≡⟨ {!!} ⟩
--   ((x⁻ ∙ (y⁻ ∙ x⁺)) ∙ z⁺) ∙ k ≡⟨ {!!} ⟩
--   (((x⁻ ∙ y⁻) ∙ x⁺) ∙ z⁺) ∙ k ≡⟨ {!!} ⟩
--   ((x⁻ ∙ y⁻) ∙ (x⁺ ∙ z⁺)) ∙ k ∎

-- _⊙_ : 𝒢 → 𝒢 → 𝒢
-- (x⁺ ⊝ x⁻) ⊙ (y⁺ ⊝ y⁻) = (x⁺ ∙ y⁺) ⊝ (x⁻ ∙ y⁻)
-- (x⁺ ⊝ x⁻) ⊙ cancel k y⁺ y⁻ z⁺ z⁻ diff i = cancel k (x⁺ ∙ y⁺) (x⁻ ∙ y⁻) (x⁺ ∙ z⁺) (x⁻ ∙ z⁻) (lemma x⁺ x⁻ y⁺ y⁻ z⁺ z⁻ k diff) i
-- cancel k x⁺ x⁻ y⁺ y⁻ diff i ⊙ (z⁺ ⊝ z⁻) = {!!}
-- cancel k w⁺ w⁻ x⁺ x⁻ diff i ⊙ cancel l y⁺ y⁻ z⁺ z⁻ diff₁ j = {!!}
