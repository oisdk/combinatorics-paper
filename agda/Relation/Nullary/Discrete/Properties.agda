{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Discrete.Properties where

open import Relation.Nullary.Discrete.Base
open import Relation.Nullary.Stable.Properties using (Stable≡→isSet)
open import Relation.Nullary.Decidable.Properties using (Dec→Stable)

open import HLevels
open import Level
open import Path

Discrete→isSet : Discrete A → isSet A
Discrete→isSet d = Stable≡→isSet (λ x y → Dec→Stable (x ≡ y) (d x y))
