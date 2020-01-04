\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Stream.Relation.Unary where

open import Codata.Stream
open import Codata.Size
open import Prelude
open import Data.List.Kleene using (_⁺; _⋆; ∹_; _&_; [])
open import Codata.Thunk
import Data.List.Kleene.Relation.Unary as Kleene
open import Data.Fin

◇ : ∀ {A : Type a} {p} (P : A → Type p) → Stream A ∞ → Type _
◇ P xs = ∃[ i ] P (xs ! i)

module Exists {a} {A : Type a} {p} (P : A → Type p) where
  push : ∀ {xs} → ◇ P (xs .tail) → ◇ P xs
  push (n , x∈xs) = (suc n , x∈xs)

  pull : ∀ {xs} → ¬ P (head xs) → ◇ P xs → ◇ P (xs .tail)
  pull ¬Px (zero  , p∈xs) = ⊥-elim (¬Px p∈xs)
  pull ¬Px (suc n , p∈xs) = (n , p∈xs)

  ++ˡ : ∀ {xs} ys → ◇ P (xs .force) → ◇ P (ys ⁺++ xs)
  ++ˡ (y & []) (n , xs) = suc n , xs
  ++ˡ (y & ∹ ys) xs =
    let n , z = ++ˡ ys xs
    in suc n , z

  ++ʳ : ∀ xs {ys} → Kleene.◇⁺ P xs → ◇ P (xs ⁺++ ys)
  ++ʳ (x & xs) (f0  , ∃Pxs) = zero , ∃Pxs
  ++ʳ (x & ∹ xs) (fs n , ∃Pxs) =
    let m , z = ++ʳ xs (n , ∃Pxs)
    in suc m , z

module Congruence {a b} {A : Type a} {B : Type b} {p q}
                  (P : A → Type p) (Q : B → Type q) {f : A → B}
                  (f↑ : ∀ {x} → P x → Q (f x)) where
  cong-◇ : ∀ xs → ◇ P xs → ◇ Q (map f xs)
  cong-◇ xs (zero , P∈xs) = zero , f↑ P∈xs
  cong-◇ xs (suc n , P∈xs) = Exists.push Q (cong-◇ (xs .tail) (n , P∈xs))

◇-concat : ∀ {p} (P : A → Type p) xs → ◇ (Kleene.◇⁺ P) xs → ◇ P (concat xs)
◇-concat P xs (zero , ps) = Exists.++ʳ P (xs .head) ps
◇-concat P xs (suc n , ps) = Exists.++ˡ P (xs .head) (◇-concat P (xs .tail) (n , ps))
\end{code}
