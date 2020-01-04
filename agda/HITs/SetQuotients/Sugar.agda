{-# OPTIONS --cubical --safe #-}

module HITs.SetQuotients.Sugar where

open import Cubical.HITs.SetQuotients
open import Prelude

private
  variable
    rᵃ : Level
    rᵇ : Level
    rᶜ : Level
    Rᵃ : A → A → Type rᵃ
    Rᵇ : B → B → Type rᵇ
    Rᶜ : C → C → Type rᶜ

