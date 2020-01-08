{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable where

open import Prelude
open import Container
open import Container.List
open import Data.Fin
open import Container.Membership (ℕ ▷ Fin)
open import Path.Reasoning
open import Data.Sigma.Properties
open import Function.Surjective.Properties
open import Data.Fin.Properties

ℰ! : Type a → Type a
ℰ! A = Σ[ xs ⦂ List A ] Π[ x ⦂ A ] x ∈ xs

ℰ!⇔Fin↠! : ℰ! A ⇔ (Σ[ n ⦂ ℕ ] (Fin n ↠! A))
ℰ!⇔Fin↠! = reassoc

ℰ!⇒Discrete : ℰ! A → Discrete A
ℰ!⇒Discrete = flip Discrete↠!A⇒Discrete⟨A⟩ discreteFin ∘ snd ∘ ℰ!⇔Fin↠! .fun
