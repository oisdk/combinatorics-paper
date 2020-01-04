{-# OPTIONS --safe --cubical #-}

module Data.Unit.UniversePolymorphic where

open import Level
import Data.Unit as Monomorphic

record ⊤ {ℓ} : Type ℓ where constructor tt

