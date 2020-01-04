{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Conat.Literals where

open import Codata.Conat
open import Literals.Number
open import Codata.Size
open import Data.Unit

instance
  numberConat : Number (Conat i)
  numberConat = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ n → ℕtoConat n
    }
