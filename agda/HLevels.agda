{-# OPTIONS --cubical --safe #-}

module HLevels where

open import Path
open import Cubical.Foundations.Everything
  using (isProp
        ;isSet
        ;isContr
        ;isProp→isSet
        ;isPropIsContr
        ;isOfHLevel
        ;isOfHLevelDep
        ;isOfHLevel→isOfHLevelDep
        )
  public
open import Cubical.HITs.SetTruncation
  using (squash₀; ∥_∥₀; ∣_∣₀; elimSetTrunc)
  public
open import Cubical.HITs.PropositionalTruncation
  using (squash; ∥_∥; ∣_∣; elimPropTrunc; recPropTrunc; elimPropTrunc→Set)
  public
