\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Stream.Relation where

open import Codata.Stream
open import Prelude
open import Agda.Builtin.Size

data Any {A : Set a} (P : A → Set b) (xs : Stream A ∞) : Set (a ℓ⊔ b) where
  here  : P (xs .head) → Any P xs
  there : Any P (xs .tail) → Any P xs
\end{code}
