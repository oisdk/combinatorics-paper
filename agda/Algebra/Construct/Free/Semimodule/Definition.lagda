\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Definition {s} (rng : Semiring s) where

open Semiring rng
\end{code}
%<*definition>
\begin{code}
infixr 5 _∶_,_
data 𝒱 {v} (V : Type v) : Type (v ℓ⊔ s) where
  []     : 𝒱 V
  _∶_,_  : (x : V) (p : 𝑅) (xs : 𝒱 V) → 𝒱 V
  -----------------------------------------------------------------------
  dup  :  ∀ x p q xs →
          x ∶ p , x ∶ q , xs ≡ x ∶ p + q , xs
  com  :  ∀ x p y q xs →
          x ∶ p , y ∶ q , xs ≡ y ∶ q , x ∶ p , xs
  del  :  ∀ x xs →
          x ∶ 0# , xs ≡ xs
  trunc : isSet (𝒱 V)
\end{code}
%</definition>
