{-# OPTIONS --safe --sized-types --without-K #-}

module Codata.Size where

open import Agda.Builtin.Size public

variable
  i j k : Size

Size≤_ : Size → Set
Size≤ i = Size< ↑ i
