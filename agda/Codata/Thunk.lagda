\begin{code}
{-# OPTIONS --sized-types --safe --cubical #-}

module Codata.Thunk where

open import Codata.Size
open import Prelude

record Thunk (A : Size → Set a) (i : Size) : Set a where
  coinductive
  constructor delay
  field
    force : ∀ {j : Size< i} → A j
open Thunk public

fix : (A : Size → Type a) → (∀ {i} → Thunk A i → A i) → ∀ {j} → A j
fix A f = f λ where .force → fix A f
\end{code}
