\begin{code}
{-# OPTIONS --cubical --safe #-}
open import Prelude
open import Algebra

-- DIJKSTRA's Algorithm?

module Algebra.Construct.Free.Semimodule.Interpretation.MonoidSemiring {m r} (mon : Monoid m) (rng : Semiring r) (sIsSet : isSet (Semiring.𝑅 rng)) where

open import Algebra.Construct.Free.Semimodule rng sIsSet

open Monoid mon
open Semiring rng

open import Path.Reasoning

𝑆[𝑀] : Type _
𝑆[𝑀] = 𝒱 𝑆

\end{code}
%<*mult>
\begin{code}
_⊗_ : 𝑆[𝑀] → 𝑆[𝑀] → 𝑆[𝑀]
xs ⊗ ys = ⦇ xs ∙ ys ⦈
\end{code}
%</mult>
\begin{code}

open import Algebra.Construct.Applicative.Monoid applicative mon

⊙0 : ∀ xs → xs ⊙ [] ≡ []
⊙0 = ∥ step ∥⇓
  where
  step : xs ∈𝒱 𝑆 ⇒∥ xs ⊙ [] ≡ [] ∥
  ∥ step ∥-prop = trunc _ _
  ∥ step ∥[] = refl
  ∥ step ∥ x ∶ p , xs ⟨ Pxs ⟩ = Pxs

⟨∪⟩⊙ : ∀ xs ys zs → (xs ∪ ys) ⊙ zs ≡ (xs ⊙ zs) ∪ (ys ⊙ zs)
⟨∪⟩⊙ xs ys zs =
  (xs ∪ ys) ⊙ zs ≡⟨⟩
  map _∙_ (xs ∪ ys) <*> zs ≡⟨ cong (_<*> zs) (map-distrib _∙_ xs ys) ⟩
  (map _∙_ xs ∪ map _∙_ ys) <*> zs ≡⟨ <*>-distribʳ (map _∙_ xs) (map _∙_ ys) zs ⟩
  (xs ⊙ zs) ∪ (ys ⊙ zs) ∎

⊙⟨∪⟩ : ∀ xs ys zs → xs ⊙ (ys ∪ zs) ≡ (xs ⊙ ys) ∪ (xs ⊙ zs)
⊙⟨∪⟩ xs ys zs = <*>-distribˡ (map _∙_ xs) ys zs


mapSemiring : Semiring _
mapSemiring = record
  { nearSemiring = record
    { 𝑅 = 𝑆[𝑀]
    ; _+_ = _∪_
    ; _*_ = _⊙_
    ; 0# = []
    ; 1# = ε ∶ 1# , []
    ; +-assoc = λ x y z → sym (∪-assoc x y z)
    ; *-assoc = ⊙-assoc
    ; 0+ = λ _ → refl
    ; +0 = ∪-idʳ
    ; 1* = ε⊙
    ; *1 = ⊙ε
    ; 0* = λ _ → refl
    ; ⟨+⟩* = ⟨∪⟩⊙
    }
  ; +-comm = ∪-comm
  ; *0 = ⊙0
  ; *⟨+⟩ = ⊙⟨∪⟩
  }
\end{code}
