\begin{code}
{-# OPTIONS --cubical --safe #-}

module Codata.Stream.Extensional.Relation.Unary where

open import Prelude
open import Codata.Stream.Extensional.Base

◇ : ∀ {p} (P : A → Type p) → Stream A → Type p
◇ P xs = ∃ (P ∘ xs)

◻ : ∀ {p} (P : A → Type p) → Stream A → Type p
◻ P xs = ∀ n → P (xs n)
\end{code}
