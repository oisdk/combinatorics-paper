\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Nat where

open import Algebra
open import Data.Nat
open import Path
open import Path.Reasoning
open import Level
open import Data.Nat.Properties

\end{code}
%<*plus-monoid>
\begin{code}
-- Proofs moved to data.nat.properties
+-mon : Monoid _
+-mon = record
  { 𝑆      = ℕ
  ; _∙_    = _+_
  ; ε      = zero
  ; assoc  = +-assoc
  ; ε∙     = +-idˡ
  ; ∙ε     = +-idʳ
  }
\end{code}
%</plus-monoid>
\begin{code}
ℕ-semiring : Semiring ℓ-zero
ℕ-semiring = record
  { nearSemiring = record
    { _+_ = _+_
    ; _*_ = _*_
    ; 0# = 0
    ; 1# = 1
    ; +-assoc = +-assoc
    ; *-assoc = *-assoc
    ; 0+ = λ _ → refl
    ; +0 = +-idʳ
    ; 1* = 1*
    ; *1 = *1
    ; 0* = λ y → refl
    ; ⟨+⟩* = ⟨+⟩*
    }
  ; +-comm = +-comm
  ; *0 = *0
  ; *⟨+⟩ = *⟨+⟩
  }
\end{code}
