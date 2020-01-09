{-# OPTIONS --cubical --safe #-}

module Relation.Unary where

open import Relation.Nullary.Decidable
open import Level

Decidable : (A → Type b) → Type _
Decidable P = ∀ x → Dec (P x)
