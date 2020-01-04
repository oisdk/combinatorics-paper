\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.MonadPlus where

open import Data.List as List
open import Algebra.List renaming (_>>=_ to _[>>=]_)
open import Data.List.Syntax
open import Prelude
\end{code}
%<*definition>
\begin{code}
mutual
  Forest : Type a → Type a
  Forest A = List (Tree A)

  data Tree (A : Type a) : Type a where
    leaf : A → Tree A
    node : Forest A → Tree A
\end{code}
%</definition>
\begin{code}
pure : A → Forest A
pure x = [ leaf x ]

mutual
  _⟦>>=⟧_ : Tree A → (A → Forest B) → Forest B
  leaf x ⟦>>=⟧ k = k x
  node   x ⟦>>=⟧ k = node (x >>= k) ∷ []

  _>>=_ : Forest A → (A → Forest B) → Forest B
  [] >>= k = []
  (x ∷ xs) >>= k = (x ⟦>>=⟧ k) ++ (xs >>= k)

0# : Forest A
0# = []

_+_ : Forest A → Forest A → Forest A
[] + ys = ys
(x ∷ xs) + ys = x ∷ (xs + ys)
\end{code}
