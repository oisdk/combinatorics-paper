\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.Construct.OrderedMonoid {ℓ} (monoid : Monoid ℓ) where

open import Prelude
open import Relation.Binary
open import Path.Reasoning

open Monoid monoid

infix 4 _≤_ _≥_
\end{code}
%<*definition>
\begin{code}
_≤_ : 𝑆 → 𝑆 → Type ℓ
x ≤ y = ∃[ z ] (y ≡ x ∙ z)
\end{code}
%</definition>
\begin{code}
_≥_ = flip _≤_
\end{code}
%<*props>
\begin{code}
≤-refl : Reflexive _≤_
≤-refl = ε , sym (∙ε _)

≤-trans : Transitive _≤_
≤-trans {x} {y} {z} (k₁ , y≡x∙k₁) (k₂ , z≡y∙k₂) = k₁ ∙ k₂ ,_ $
  z ≡⟨ z≡y∙k₂ ⟩
  y ∙ k₂ ≡⟨ cong (_∙ k₂) y≡x∙k₁ ⟩
  (x ∙ k₁) ∙ k₂ ≡⟨ assoc x k₁ k₂ ⟩
  x ∙ (k₁ ∙ k₂) ∎

ε≤x : ∀ x → ε ≤ x
ε≤x x = x , sym (ε∙ x)

∙-cong : ∀ x {y z} → y ≤ z → x ∙ y ≤ x ∙ z
∙-cong x (k , z≡y∙k) = k , cong (x ∙_) z≡y∙k ; sym (assoc x _ k)

\end{code}
%</props>
