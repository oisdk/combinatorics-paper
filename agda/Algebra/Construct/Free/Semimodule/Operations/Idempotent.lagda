\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Algebra.Construct.Free.Semimodule.Operations.Idempotent {s} (rng : IdempotentSemiring s) where

open IdempotentSemiring rng
open import Algebra.Construct.Free.Semimodule.Definition semiring
open import Algebra.Construct.Free.Semimodule.Eliminators semiring
open import Algebra.Construct.Free.Semimodule.Operations.Union semiring
\end{code}
%<*proof>
\begin{code}
∪-idem : (xs : 𝒱 A) → xs ∪ xs ≡ xs
∪-idem = ∥ ∪-idem′ ∥⇓
  where
  ∪-idem′ : xs ∈𝒱 A ⇒∥ xs ∪ xs ≡ xs ∥
  ∥ ∪-idem′ ∥-prop              = trunc _ _
  ∥ ∪-idem′ ∥[]                 = refl
  ∥ ∪-idem′ ∥ x ∶ p , xs ⟨ P ⟩  =
    (x ∶ p , xs) ∪ x ∶ p , xs
              ≡⟨ ∪-cons p x (x ∶ p , xs) xs ⟩
    x ∶ p , (x ∶ p , xs) ∪ xs
              ≡⟨ cong (_∪ xs) (dup x p p xs) ⟩
    x ∶ (p + p) , xs ∪ xs
              ≡⟨ cong (x ∶_, xs ∪ xs) (+-idem p) ⟩
    x ∶ p , xs ∪ xs
              ≡⟨ cong (x ∶ p ,_) P ⟩
    x ∶ p , xs ∎
\end{code}
%</proof>
