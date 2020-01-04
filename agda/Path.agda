{-# OPTIONS --cubical --safe #-}

module Path where

open import Cubical.Foundations.Everything
  using ( _≡_
        ; sym
        ; refl
        ; subst
        ; transport
        ; Path
        ; PathP
        ; I
        ; i0
        ; i1
        ; funExt
        ; cong
        ; toPathP
        ; transp
        ; cong₂
        ; ~_
        )
  renaming (_∙_ to _;_)
  public

open import Relation.Nullary using (¬_)
open import Level

infix 4 _≢_
_≢_ : {A : Type a} → A → A → Type a
x ≢ y = ¬ (x ≡ y)

infix 4 PathP-syntax PathP-lambda-syntax
PathP-syntax = PathP
PathP-lambda-syntax = PathP

syntax PathP-syntax T lhs rhs = lhs ≡[ T ]≡ rhs
syntax PathP-lambda-syntax (λ i → T) lhs rhs = lhs ≡[ i ≔ T ]≡ rhs

