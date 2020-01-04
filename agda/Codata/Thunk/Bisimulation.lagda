\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Thunk.Bisimulation where

open import Codata.Thunk
open import Codata.Size
open import Prelude


infix 4 ⌈_⌉_≋_
record ⌈_⌉_≋_ (i : Size) {A : Size → Type a} (xs ys : Thunk A i) : Type a where
  field
    force-≋ : ∀ {j : Size< i} → xs .force {j} ≡ ys .force {j}
open ⌈_⌉_≋_ public

bisim : ∀ (A : Size → Type a) {i : Size} {xs ys : Thunk A i} → ⌈ i ⌉ xs ≋ ys → xs ≡ ys
bisim _ xs≋ys i .force {j} = xs≋ys .force-≋ {j} i
\end{code}
