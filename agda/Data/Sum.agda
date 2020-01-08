{-# OPTIONS --cubical --safe #-}

module Data.Sum where

open import Level

data _+_ {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inl : A → A + B
  inr : B → A + B
