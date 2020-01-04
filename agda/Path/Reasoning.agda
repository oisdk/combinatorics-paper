{-# OPTIONS --cubical --safe #-}

module Path.Reasoning where

open import Path

open import Level

infixr 2 ≡˘⟨⟩-syntax _≡⟨⟩_ ≡⟨∙⟩-syntax

≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≡ z → y ≡ x → x ≡ z
≡˘⟨⟩-syntax _ y≡z y≡x = sym y≡x ; y≡z

syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨∙⟩-syntax _ y≡z x≡y = x≡y ; y≡z

syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_≡⟨⟩_ : ∀ (x : A) {y} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infix 1 begin[_]_
begin[_]_ : ∀ {a} {A : Set a} {x y : A} → I → x ≡ y → A
begin[ i ] x≡y = x≡y i

infix 3 _∎
_∎ : ∀ {A : Set a} (x : A) → x ≡ x
_∎ x = λ _ → x
{-# INLINE _∎ #-}
