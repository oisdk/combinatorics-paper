\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable.Container where

open import Prelude
open import Container
open import Container.List
open import Data.Fin
open import Container.Membership (ℕ ▷ Fin)
open import Path.Reasoning
open import Data.Sigma.Properties
open import Function.Surjective.Properties
open import Data.Fin.Properties
\end{code}
%<*split-enum-def>
\begin{code}
ℰ! : Type a → Type a
ℰ! A = Σ[ xs ⦂ List A ] ((x : A) → x ∈ xs)
\end{code}
%</split-enum-def>
