{-# OPTIONS --cubical --safe #-}

module Data.Nat.Base where

open import Agda.Builtin.Nat public
  using (_+_; _*_; zero; suc)
  renaming (Nat to ℕ)
