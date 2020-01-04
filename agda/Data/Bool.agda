{-# OPTIONS --cubical --safe #-}

module Data.Bool where

open import Level
open import Agda.Builtin.Bool using (Bool; true; false) public
open import Data.Unit
open import Data.Empty

bool : ∀ {ℓ} {P : Bool → Type ℓ} (f : P false) (t : P true) → (x : Bool) → P x
bool f t false = f
bool f t true = t

bool′ : ∀ {a} {A : Type a} (f t : A) → Bool → A
bool′ = bool

not : Bool → Bool
not false = true
not true = false

infixl 6 _∨_
_∨_ : Bool → Bool → Bool
false ∨ y = y
true  ∨ y = true

infixl 7 _∧_
_∧_ : Bool → Bool → Bool
false ∧ y = false
true  ∧ y = y

infixr 0 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then x else _ = x
if false then _ else x = x

T : Bool → Type₀
T true  = ⊤
T false = ⊥
