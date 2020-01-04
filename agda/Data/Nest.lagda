\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Nest where

open import Prelude

_^_ : (Set a → Set a) → ℕ → Set a → Set a
(F ^ zero ) A = A
(F ^ suc n) A = (F ^ n) (F A)

Nest : (Set a → Set a) → Set a → ℕ → Set a
Nest F A n = (F ^ n) A
\end{code}
