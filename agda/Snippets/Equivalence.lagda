\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Equivalence where

open import Level
open import Data.Sigma
open import HLevels
open import Cubical.Foundations.Equiv using (fiber)

module _ {A : Type a} {B : Type b} where
\end{code}
%<*is-equiv-def>
\begin{code}
  isEquiv : (f : A → B) → Type _
  isEquiv f = (y : B) → isContr (fiber f y)
\end{code}
%</is-equiv-def>
\begin{code}
_≃_ : Type a → Type b → Type _
\end{code}
%<*equiv-def>
\begin{code}
A ≃ B = Σ[ f ⦂ (A → B) ] isEquiv f
\end{code}
%</equiv-def>
