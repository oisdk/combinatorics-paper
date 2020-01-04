\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Vec.Iterated.NonEmpty where

open import Prelude hiding (tt; ⊤)
open import Data.Unit.UniversePolymorphic

Vec⁺ : ∀ {a} (A : Type a) → ℕ → Type a
Vec⁺ A zero = A
Vec⁺ A (suc n) = A × Vec⁺ A n

Vec : ∀ {a} (A : Type a) → ℕ → Type a
Vec _ zero = ⊤
Vec A (suc n) = Vec⁺ A n

-- map⁺ : ∀ {n} → (A → B) → Vec⁺ A n → Vec
-- map : ∀ {n} → (A → B) → Vec A n → Vec B n
-- map {n = zero} f xs = tt
-- map {n = suc n} f xs = {!!}
\end{code}
