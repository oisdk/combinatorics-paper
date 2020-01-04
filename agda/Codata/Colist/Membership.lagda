\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Colist.Membership where

open import Prelude
open import Codata.Size
open import Codata.Colist
open import Codata.Conat
open import Codata.Cofin
open import Codata.Thunk
open import Relation.Nullary
open import Function.Injective
open import Codata.Colist.Relation.Unary

module _ {a} {A : Type a} {x : A} where open Exists (_≡ x) public

infixr 5 _∈_ _∉_
_∈_ _∉_ : A → Colist A ∞ → Type _
x ∈ xs = ◇ (_≡ x) xs
x ∉ xs = ¬ (x ∈ xs)

cong-∈ : ∀ (f : A → B) {x : A} xs → x ∈ xs → f x ∈ map f xs
cong-∈ f {x = x} = Congruence.cong-any (_≡ x) (_≡ f x) (cong f)

fin∈tabulate : ∀ {n} → (f : Cofin n → A) → (i : Cofin n) → f i ∈ tabulate n f
fin∈tabulate f zero     = zero , refl
fin∈tabulate f (suc i)  = push (fin∈tabulate (f ∘ suc) i)
\end{code}
