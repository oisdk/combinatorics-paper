{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Base where

open import Level

data Maybe (A : Type a) : Type a where
  nothing : Maybe A
  just : A → Maybe A
