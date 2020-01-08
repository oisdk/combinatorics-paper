{-# OPTIONS --cubical --safe #-}

module Function.Isomorphism where

open import Cubical.Foundations.Isomorphism using (Iso; section; retract; isoToPath; iso) public

open Iso public

infix 4 _⇔_
_⇔_ = Iso
