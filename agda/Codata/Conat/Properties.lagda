\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Conat.Properties where

open import Codata.Conat
open import Codata.Size
open import Codata.Thunk
open import Prelude
open import Codata.Conat.Bisimulation

∞+∞≋∞ : ∀ {i} → ⌈ i ⌉ inf + inf ≋ inf
∞+∞≋∞ = suc-≋ λ where .force-≋ → ∞+∞≋∞

\end{code}
