\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Tree.Perfect where

open import Data.Nest
open import Prelude

Pair : Set a → Set a
Pair A = A × A

Perfect : Set a → ℕ → Set a
Perfect = Nest Pair
\end{code}
