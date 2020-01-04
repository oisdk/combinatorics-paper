\begin{code}

{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Relation.Binary
import Algebra.Construct.OrderedMonoid as OrdMon

module Algebra.Search.MonoidalHeap {s} (mon : Monoid s) (_≤?_ : Total (OrdMon._≤_ mon)) where

open Monoid mon
open OrdMon mon

open import Prelude
open import Data.List using (List; _∷_; [])

𝒮 : Type s
𝒮 = 𝑆 → 𝑆

⟦_⇑⟧ : 𝑆 → 𝒮
⟦_⇑⟧ = _∙_

⟦_⇓⟧ : 𝒮 → 𝑆
⟦ x ⇓⟧ = x ε

infixr 6 _∹_&_
record Heap⁺ {v} (V : 𝑆 → Type v) : Type (v ℓ⊔ s) where
  constructor _∹_&_
  inductive
  field
    key : 𝑆
    val : V key
    children : List (Heap⁺ (V ∘ _∙_ key))
open Heap⁺ public

data Heap (V : 𝑆 → Type a) : Type (a ℓ⊔ s) where
  leaf : Heap V
  node : Heap⁺ V → Heap V

private
  variable
    v : Level
    V : 𝑆 → Type v

lemma : ∀ x y k → x ≡ y ∙ k → ⟦ x ⇑⟧ ≡ ⟦ y ⇑⟧ ∘ ⟦ k ⇑⟧
lemma x y k x≡y∙k i z = (cong (_∙ z) x≡y∙k ; assoc y k z) i

merge⁺ : Heap⁺ V → Heap⁺ V → Heap⁺ V
merge⁺ {V = V} (x ∹ xv & xs) (y ∹ yv & ys) with x ≤? y
... | inl (k , x≤y) = x ∹ xv & (k ∹ subst V x≤y yv & subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma y x k x≤y) ys ∷ xs)
... | inr (k , x≥y) = y ∹ yv & (k ∹ subst V x≥y xv & subst (List ∘ Heap⁺ ∘ _∘_ V) (lemma x y k x≥y) xs ∷ ys)

merge : Heap V → Heap V → Heap V
merge leaf ys = ys
merge (node xs) leaf = node xs
merge (node xs) (node ys) = node (merge⁺ xs ys)

mergeQs⁺ : Heap⁺ V → List (Heap⁺ V) → Heap⁺ V
mergeQs⁺ x₁ [] = x₁
mergeQs⁺ x₁ (x₂ ∷ []) = merge⁺ x₁ x₂
mergeQs⁺ x₁ (x₂ ∷ x₃ ∷ xs) = merge⁺ (merge⁺ x₁ x₂) (mergeQs⁺ x₃ xs)

mergeQs : List (Heap⁺ V) → Heap V
mergeQs [] = leaf
mergeQs (x ∷ xs) = node (mergeQs⁺ x xs)

singleton⁺ : ∀ x → V x → Heap⁺ V
singleton⁺ x xv .key = x
singleton⁺ x xv .val = xv
singleton⁺ x xv .children = []

singleton : ∀ x → V x → Heap V
singleton x xv = node (singleton⁺ x xv)

insert⁺ : ∀ x → V x → Heap⁺ V → Heap⁺ V
insert⁺ x xv = merge⁺ (singleton⁺ x xv)

insert : ∀ x → V x → Heap V → Heap V
insert x xv leaf = singleton x xv
insert x xv (node xs) = node (insert⁺ x xv xs)

minView : Heap V → Maybe (∃[ p ] V p × Heap (V ∘ ⟦ p ⇑⟧))
minView leaf = nothing
minView (node (x ∹ xv & xs)) = just (x , xv , mergeQs xs)

module Listed where
  data Sorted (V : 𝑆 → Set v) : Set (v ℓ⊔ s) where
    [] : Sorted V
    _∹_&_ : ∀ x → (xv : V x) → (xs : Sorted (V ∘ ⟦ x ⇑⟧)) → Sorted V

  -- {-# TERMINATING #-}
  -- fromHeap : Heap V → Sorted V
  -- fromHeap hp with minView hp
  -- ... | nothing = []
  -- ... | just (x , xv , xs) =  x ∹ xv & fromHeap xs
