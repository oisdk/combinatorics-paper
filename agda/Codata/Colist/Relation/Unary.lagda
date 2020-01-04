\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Colist.Relation.Unary where

open import Codata.Colist
open import Codata.Size
open import Prelude
open import Data.List.Kleene as Kleene using (_&_; _⋆; _⁺; []; ∹_)
import Data.List.Kleene.Relation.Unary as Kleene
open import Codata.Cofin
open import Data.Fin
open import Codata.Thunk

private
  variable
    p : Level


◇ : ∀ {A : Type a} (P : A → Type p) → Colist A ∞ → Type _
◇ P xs = ∃[ i ] P (xs ! i)

◇⁺ : ∀ {A : Type a} (P : A → Type p) → Colist⁺ A ∞ → Type _
◇⁺ P xs = ∃[ i ] P (xs !⁺ i)

module Exists {a} {A : Type a} {p} (P : A → Type p) where
  push : ∀ {xs} → ◇ P (xs .tail) → ◇⁺ P xs
  push (n , x∈xs) = (suc n , x∈xs)

  pull : ∀ {x xs} → ¬ P x → ◇⁺ P (x & xs) → ◇ P xs
  pull ¬Px (zero  , p∈xs) = ⊥-elim (¬Px p∈xs)
  pull ¬Px (suc n , p∈xs) = (n , p∈xs)

  ++ˡ : ∀ {xs} ys → ◇ P (xs .force) → ◇⁺ P (ys ⁺++ xs)
  ++ˡ (y & []) (n , xs) = suc n , xs
  ++ˡ (y & ∹ ys) xs =
    let n , z = ++ˡ ys xs
    in suc n , z

  ++ʳ : ∀ xs {ys} → Kleene.◇⁺ P xs → ◇⁺ P (xs ⁺++ ys)
  ++ʳ (x & xs) (f0  , ∃Pxs) = zero , ∃Pxs
  ++ʳ (x & ∹ xs) (fs n , ∃Pxs) =
    let m , z = ++ʳ xs (n , ∃Pxs)
    in suc m , z

◻ : ∀ {A : Type a} (P : A → Type p) → Colist A ∞ → Type _
◻ P xs = ∀ i → P (xs ! i)

module Forall {a} {A : Type a} {p} (P : A → Type p) where

  push : ∀ {xs} → P (xs .head) → ◻ P (xs .tail) → ◻ P (∹ xs)
  push Px xs zero = Px
  push Px xs (suc n) = xs n

  empty : ◻ P []
  empty ()

module Congruence {a b} {A : Type a} {B : Type b} {p q}
                  (P : A → Type p) (Q : B → Type q) {f : A → B}
                  (f↑ : ∀ {x} → P x → Q (f x)) where
  cong-any : ∀ xs → ◇ P xs → ◇ Q (map f xs)
  cong-any (∹ xs) (zero , P∈xs) = zero , f↑ P∈xs
  cong-any (∹ xs) (suc n , P∈xs) = Exists.push Q (cong-any (xs .tail) (n , P∈xs))

◇-concat : ∀ {p} (P : A → Type p) xs → ◇ (Kleene.◇⁺ P) xs → ◇ P (concat xs)
◇-concat P (∹ xs) (zero , ps) = Exists.++ʳ P (xs .head) ps
◇-concat P (∹ xs) (suc n , ps) = Exists.++ˡ P (xs .head) (◇-concat P (xs .tail) (n , ps))

open import Data.List as List using (List; _∷_; [])
import Data.List.Relation.Unary as List

◇List⇒◇Colist : ∀ {a} {A : Type a} {p} (P : A → Type p)
                  → ∀ xs → List.◇ P xs → ◇ P (ListToColist xs)
◇List⇒◇Colist P (x ∷ xs) (f0 , P∈xs) = zero , P∈xs
◇List⇒◇Colist P (x ∷ xs) (fs n , P∈xs) = Exists.push P (◇List⇒◇Colist P xs (n , P∈xs))

import Data.List.Relation.Unary as List

module Search {A : Type a} where
  data Found {p} (P : A → Type p) (xs : Colist A ∞) : Type (a ℓ⊔ p) where
    none :  ◻ (¬_ ∘ P) xs → Found P xs
    one  :  ◇ P xs → Found P xs
    upTo : ∀ n → List.◻ (¬_ ∘ P) (take n xs) → Found P xs

  module _ {p} {P : A → Type p} (P? : ∀ x → Dec (P x)) where
    search : ℕ → ∀ xs → Found P xs
    search zero xs = upTo zero λ ()
    search (suc n) [] = none (Forall.empty (¬_ ∘ P))
    search (suc n) (∹ xs) with P? (xs .head)
    search (suc n) (∹ xs) | yes p = one (zero , p)
    search (suc n) (∹ xs) | no ¬p with search n (xs .tail)
    search (suc n) (∹ xs) | no ¬p | none ¬ps = none λ { zero → ¬p ; (suc i) → ¬ps i}
    search (suc n) (∹ xs) | no ¬p | one x = one (Exists.push P x)
    search (suc n) (∹ xs) | no ¬p | upTo m x = upTo (suc m) (maybe x ¬p)

module Test {A : Type a} where
  data Tested {p} (P : A → Type p) (xs : Colist A ∞) : Type (a ℓ⊔ p) where
    pass :  ◻ P xs → Tested P xs
    fail :  ◇ (¬_ ∘ P) xs → Tested P xs
    upTo : ∀ n → List.◻ P (take n xs) → Tested P xs

  module _ {p} {P : A → Type p} (P? : ∀ x → Dec (P x)) where
    test : ℕ → ∀ xs → Tested P xs
    test zero xs = upTo zero λ ()
    test (suc n) [] = pass λ ()
    test (suc n) (∹ xs) with P? (xs .head)
    test (suc n) (∹ xs) | no ¬p = fail (zero , ¬p)
    test (suc n) (∹ xs) | yes p with test n (xs .tail)
    test (suc n) (∹ xs) | yes p | pass ps = pass λ { zero → p ; (suc i) → ps i}
    test (suc n) (∹ xs) | yes p | fail x = fail (Exists.push (¬_ ∘ P) x)
    test (suc n) (∹ xs) | yes p | upTo m x = upTo (suc m) (maybe x p)
\end{code}
