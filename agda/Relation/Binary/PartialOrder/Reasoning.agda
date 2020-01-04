{-# OPTIONS --safe --cubical #-}

open import Relation.Binary

module Relation.Binary.PartialOrder.Reasoning {a} {𝑆 : Set a} {b} (partialOrder : PartialOrder 𝑆 b) where

open PartialOrder partialOrder
open import Function
open import Path using (_≡_; subst; sym)

infixr 2 ≤⟨∙⟩-syntax ≡⟨∙⟩-syntax ≡˘⟨∙⟩-syntax
≤⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≤ z → x ≤ y → x ≤ z
≤⟨∙⟩-syntax _ y≤z x≤y = x≤y ⟨ trans ⟩ y≤z

syntax ≤⟨∙⟩-syntax x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z

≡⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≤ z → x ≡ y → x ≤ z
≡⟨∙⟩-syntax x {y} {z} y≤z x≡y = subst (_≤ z) (sym x≡y) y≤z

syntax ≡⟨∙⟩-syntax x y≤z x≡y = x ≡⟨ x≡y ⟩ y≤z

≡˘⟨∙⟩-syntax : ∀ (x : 𝑆) {y z} → y ≤ z → y ≡ x → x ≤ z
≡˘⟨∙⟩-syntax x {y} {z} y≤z y≡x = subst (_≤ z) y≡x y≤z

syntax ≡˘⟨∙⟩-syntax x y≤z x≡y = x ≡˘⟨ x≡y ⟩ y≤z

infix 3 _∎
_∎ : ∀ x → x ≤ x
x ∎ = refl
