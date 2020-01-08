{-# OPTIONS --cubical --safe #-}

module Function.Fiber where

open import Level
open import Data.Sigma.Base
open import Path

fiber : (A → B) → B → Type _
fiber f y = ∃[ x ] f x ≡ y
