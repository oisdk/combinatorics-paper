\begin{code}
{-# OPTIONS --cubical --safe --sized-types --postfix-projections #-}

module Codata.Stream.Bisimulation where

open import Prelude
open import Codata.Stream
open import Codata.Size

infix 4 ⌈_⌉_≋_
record ⌈_⌉_≋_ (i : Size) {A : Type a} (xs ys : Stream A i) : Type a where
  coinductive
  field
    head-≡ : xs .head ≡ ys .head
    tail-≋ : ∀ {j : Size< i} → ⌈ j ⌉ xs .tail ≋ ys .tail
open ⌈_⌉_≋_ public

≋-refl : ∀ (xs : Stream A i) → ⌈ i ⌉ xs ≋ xs
≋-refl xs .head-≡ = refl
≋-refl xs .tail-≋ = ≋-refl (xs .tail)

≋⇒≡ : ∀ {xs ys : Stream A i} → ⌈ i ⌉ xs ≋ ys → xs ≡ ys
≋⇒≡ xs≋ys i .head = xs≋ys .head-≡ i
≋⇒≡ xs≋ys i .tail {j} = ≋⇒≡ (xs≋ys .tail-≋ {j}) i
\end{code}
