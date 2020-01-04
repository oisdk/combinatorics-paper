{-# OPTIONS --cubical --safe #-}

module Algebra.Bool where

open import Algebra
open import Data.Bool
open import Prelude


semiringBool : Semiring _
semiringBool = record
  { nearSemiring = record
    { 𝑅 = Bool
    ; _*_ = _∧_
    ; 1# = true
    ; 0# = false
    ; _+_ = _∨_
    ; 1* = λ _ → refl
    ; *1 = bool refl refl
    ; 0* = λ _ → refl
    ; +-assoc = bool (λ _ _ → refl) (λ _ _ → refl)
    ; *-assoc = bool (λ _ _ → refl) (λ _ _ → refl)
    ; 0+ = λ _ → refl
    ; +0 = bool refl refl
    ; ⟨+⟩* = bool (λ _ _ → refl) (bool (bool refl refl) (bool refl refl))
    }
  ; +-comm = bool (bool refl refl) (bool refl refl)
  ; *0 = bool refl refl
  ; *⟨+⟩ = bool (λ _ _ → refl) (λ _ _ → refl)
  }
