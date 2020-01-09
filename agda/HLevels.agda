{-# OPTIONS --cubical --safe #-}

module HLevels where

open import Path
open import Cubical.Foundations.Everything
  using (isProp
        ;isSet
        ;isContr
        ;isPropIsContr
        ;isProp→isSet
        ;isOfHLevel→isOfHLevelDep
        ;hProp
        ;isSetHProp
        ;isPropIsProp
        )
  public
