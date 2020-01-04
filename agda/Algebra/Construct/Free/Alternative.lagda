\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Alternative where

open import Data.List
open import Prelude hiding (A; B)

variable
  A : Type a
  B : Type a
\end{code}
%<*definition>
\begin{code}
mutual
  Forest : Type a → Type (ℓ-suc a)
  Forest A = List (Tree A)

  data Tree (A : Type a) : Type (ℓ-suc a) where
    leaf : A → Tree A
    _◂_  : {B : Type a}
         → (B → A)
         → Forest B
         → Tree A
\end{code}
%</definition>
