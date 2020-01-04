\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Algebra.Construct.Free.Semimodule.Operations.Expect {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations.Condition rng
open import Probability.Giry rng using (𝒢)
\end{code}
%<*giry>
\begin{code}
∫ : 𝒱 A → 𝒢 A
∫ = λ xs f → [ ∮ f ]↓ xs
  where
  ∮ : (A → 𝑅) → A ↘ 𝑅
  [ ∮ f ] x ∶ p , xs = f x * p + xs
  [ ∮ f ][] = 0#
\end{code}
%</giry>
\begin{code}
  [ ∮ f ]-dup x p q xs =
    f x * p + (f x * q + xs)  ≡˘⟨ +-assoc (f x * p) (f x * q) xs ⟩
    (f x * p + f x * q) + xs  ≡˘⟨ cong (_+ xs) (*⟨+⟩ (f x) p q) ⟩
    f x * (p + q) + xs ∎
  [ ∮ f ]-com x p y q xs =
    f x * p + (f y * q + xs)  ≡˘⟨ +-assoc (f x * p) (f y * q) (xs) ⟩
    (f x * p + f y * q) + xs  ≡⟨ cong (_+ xs) (+-comm (f x * p) (f y * q)) ⟩
    (f y * q + f x * p) + xs  ≡⟨ +-assoc (f y * q) (f x * p) (xs) ⟩
    f y * q + (f x * p + xs) ∎
  [ ∮ f ]-del x xs =
    f x * 0# + xs  ≡⟨ cong (_+ xs) (*0 (f x)) ⟩
    0# + xs        ≡⟨ 0+ xs ⟩
    xs ∎
  [ ∮ f ]-set = sIsSet
syntax ∫ xs (λ x → e) = ∫[ xs ] e 𝑑 x

-- ⋊-distrib-∫ : ∀ n (xs : A *) f → (∫ (n ⋊ xs) f) ≡ (∫[ xs ] (n * f x) 𝑑 x)
-- ⋊-distrib-∫ = {!!}

-- ⋊-distrib-∫′ : ∀ n (xs : A *) f → (∫ (n ⋊ xs) f) ≡ n * ∫ xs f
-- ⋊-distrib-∫′ = {!!}

\end{code}
