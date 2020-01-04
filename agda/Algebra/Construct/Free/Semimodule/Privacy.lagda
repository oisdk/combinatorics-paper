\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Privacy {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open import Algebra.Construct.Free.Semimodule rng sIsSet

open Semiring rng

\end{code}
%<*alg-def>
\begin{code}
_⊸_ : Type a → Type b → Type _
A ⊸ B = A → 𝒱 B
\end{code}
%</alg-def>
%<*subset>
\begin{code}
⊆_ : Type a → Type _
⊆ A = A → 𝑅
\end{code}
%</subset>
%<*pr>
\begin{code}
Pr[_∈_] : 𝒱 A → ⊆ A → 𝑅
Pr[_∈_] = ∫
\end{code}
%</pr>
\begin{code}
im : (A ⊸ B) → Type _
im {B = B} _ = B

module _ (_≡_∪｛𝑑｝ : A → A → Type₀) (exp : 𝑅 → 𝑅) (lte : 𝑅 → 𝑅 → Type₀) where
 infix 4 _≤_
 _≤_ = lte
\end{code}
%<*private>
\begin{code}
 _-private : 𝑅 → (A ⊸ B) → Type _
 ε -private = λ 𝒜 →
   ∀ 𝐷₁ 𝐷₂ → (𝐷₁ ≡ 𝐷₂ ∪｛𝑑｝) →
   ∀ (𝑆 : ⊆ im 𝒜) →
   Pr[ 𝒜 𝐷₁ ∈  𝑆 ] ≤ exp ε * Pr[ 𝒜 𝐷₂ ∈ 𝑆 ]
\end{code}
%</private>
