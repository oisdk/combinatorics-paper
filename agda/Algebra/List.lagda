\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.List where

open import Algebra
open import Data.List
open import Prelude
\end{code}
\begin{code}
freeMonoid : ∀ {a} → Type a → Monoid a
freeMonoid A = record
  { 𝑆 = List A
  ; _∙_ = _++_
  ; assoc = ++-assoc
  ; ε∙ = λ _ → refl
  ; ∙ε = ++[]
  }
\end{code}
%<*interp>
\begin{code}
module _ {m} (mon : Monoid m) where
  open Monoid mon
  ⟦_⟧ : (A → 𝑆) → List A → 𝑆
  ⟦ h ⟧ [] = ε
  ⟦ h ⟧ (x ∷ xs) = h x ∙ ⟦ h ⟧ xs
\end{code}
%</interp>
\begin{code}
_>>=_ : List A → (A → List B) → List B
xs >>= f = foldr (λ x xs → f x ++ xs) [] xs
\end{code}
