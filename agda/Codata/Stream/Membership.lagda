\begin{code}
{-# OPTIONS --cubical --sized-types --safe #-}

module Codata.Stream.Membership where

open import Prelude
open import Codata.Stream
open import Agda.Builtin.Size
open import Codata.Stream.Relation.Unary

module _ {a} {A : Type a} {x : A} where open Exists (_≡ x) public

infixr 5 _∈_ _∉_
_∈_ _∉_ : A → Stream A ∞ → Type _
x ∈ xs = ◇ (_≡ x) xs
x ∉ xs = ¬ (x ∈ xs)

cong-∈ : ∀ (f : A → B) {x : A} xs → x ∈ xs → f x ∈ map f xs
cong-∈ f {x = x} = Congruence.cong-◇ (_≡ x) (_≡ f x) (cong f)

n∈tabulate : (f : ℕ → A) → ∀ i → f i ∈ tabulate f
n∈tabulate f zero     = zero , refl
n∈tabulate f (suc i)  = push (n∈tabulate (f ∘ suc) i)
\end{code}
