{-# OPTIONS --without-K --safe #-}

module Data.Maybe where

open import Level

data Maybe (A : Type a) : Type a where
  nothing : Maybe A
  just : A → Maybe A

maybe : ∀ {A : Type a} {B : Maybe A → Type b} →
          ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n

maybe′ : (A → B) → B → Maybe A → B
maybe′ = maybe

map : (A → B) → Maybe A → Maybe B
map f nothing = nothing
map f (just x) = just (f x)
