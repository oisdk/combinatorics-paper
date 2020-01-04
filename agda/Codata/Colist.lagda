\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Colist where

open import Codata.Size
open import Prelude
open import Codata.Thunk
open import Codata.Conat
open import Codata.Cofin
open import Data.List.Kleene using (_⁺; _⋆; head; tail; []; ∹_)
\end{code}
%<*def>
\begin{code}
mutual
  infixr 5 _&_ ∹_
  data Colist (A : Set a) (i : Size) : Set a where
    [] : Colist A i
    ∹_ : Colist⁺ A i → Colist A i

  record Colist⁺ (A : Set a) (i : Size) : Set a where
    coinductive
    constructor _&_
    field
      head : A
      tail : ∀ {j : Size< i} → Colist A j
\end{code}
%</def>
\begin{code}
open Colist⁺ public

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : Size → Set ℓ₂) where
 mutual
  foldr : ∀ {i}
        → (∀ {j : Size≤ i} → A → Thunk B j → B j)
        → (∀ {j : Size≤ i} → B j)
        → Colist A i
        → B i
  foldr _ b [] = b
  foldr f b (∹ xs) = foldr⁺ f b xs

  foldr⁺ : ∀ {i}
         → (∀ {j : Size≤ i} → A → Thunk B j → B j)
         → (∀ {j : Size≤ i} → B j)
         → Colist⁺ A i
         → B i
  foldr⁺ f b xs = f (head xs) λ where .force → foldr f b (xs .tail)

mutual
  length : ∀ {i} → Colist A i → Conat i
  length [] = zero
  length (∹ xs) = length⁺ xs

  length⁺ : ∀ {i} → Colist⁺ A i → Conat i
  length⁺ xs = suc λ where .force → length (xs .tail)

infixl 6 _!_ _!⁺_
mutual
  _!_ : (xs : Colist A ∞) → Cofin (length xs) → A
  (∹ xs) ! n = xs !⁺ n

  _!⁺_ : (xs : Colist⁺ A ∞) → Cofin (length⁺ xs) → A
  xs !⁺ zero  = head xs
  xs !⁺ suc n = xs .tail ! n

mutual
  map : ∀ {i} → (A → B) → Colist A i → Colist B i
  map f [] = []
  map f (∹ xs) = ∹ map⁺ f xs

  map⁺ : ∀ {i} → (A → B) → Colist⁺ A i → Colist⁺ B i
  head (map⁺ f xs) = f (head xs)
  tail (map⁺ f xs) = map f (tail xs)

infixr 5 _⁺++_ _⋆++_
mutual
  _⁺++_ : A ⁺ → Thunk (Colist A) i → Colist⁺ A i
  (xs ⁺++ ys) .head = xs .head
  (xs ⁺++ ys) .tail = xs .tail ⋆++ ys .force

  _⋆++_ : A ⋆ → Colist A i → Colist A i
  []     ⋆++ ys = ys
  (∹ xs) ⋆++ ys = ∹ xs ⁺++ λ where .force → ys

concat : Colist (A ⁺) i → Colist A i
concat = foldr (Colist _) (λ xs ys → ∹ xs ⁺++ ys) []

mutual
  tabulate : ∀ n → (f : Cofin n → A) → Colist A i
  tabulate zero    f = []
  tabulate (suc x) f = ∹ tabulate⁺ x f

  tabulate⁺ : ∀ n → (Cofin (suc n) → A) → Colist⁺ A i
  tabulate⁺ n f .head = f zero
  tabulate⁺ n f .tail = tabulate (n .force) (f ∘ suc)


map-length : ∀ (f : A → B) (xs : Colist A i) → length {i = i} xs ≡ length {i = i} (map {i = i} f xs)
map-length {A = A} {B = B} f xs = bisim (go xs)
  where
  open import Codata.Conat.Bisimulation

  go : (xs : Colist A i) →  ⌈ i ⌉ length {i = i} xs ≋ length {i = i} (map {i = i} f xs)
  go [] = zero-≋
  go (∹ xs) = suc-≋ λ where .force-≋ → go (xs .tail)

open import Data.List as List

ListToColist : List A → Colist A i
ListToColist = List.foldr (λ x xs → ∹ λ where .head → x ; .tail → xs) []

take : ℕ → Colist A ∞ → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (∹ xs) = xs .head ∷ take n (xs .tail)
\end{code}
