{-# OPTIONS --cubical --safe #-}

module Path where

open import Cubical.Foundations.Prelude public
  using ( refl
        ; sym
        ; cong
        )
  renaming (_∙_ to _;_)
open import Agda.Builtin.Cubical.Path public
  using ( _≡_
        ; PathP
        )
