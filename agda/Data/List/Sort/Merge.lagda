\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Relation.Binary
open import Prelude hiding (tt)

module Data.List.Sort.Merge {e} {E : Type e} {r} (totalOrder : TotalOrder E r) where

open import Relation.Binary.Construct.LowerBound totalOrder

open TotalOrder totalOrder renaming (refl to refl-≤)
open TotalOrder lb-ord renaming (trans to ⌊trans⌋) using ()

open import Data.List


open import Data.List.Relation.Binary.Permutation
open import Data.Unit.UniversePolymorphic as Poly using (tt)
open import Function.Isomorphism
open import Data.Fin
open import Data.List.Membership

mutual
  merge-on : (x : E) (xs : List E) (y : E) (ys : List E) →
             (x ≤ y) ⊎ (y ≤ x) →
             List E
  merge-on x xs y ys (inl x₁) = x ∷ merge⁺ y ys xs
  merge-on x xs y ys (inr x₁) = y ∷ merge⁺ x xs ys

  merge : List E → List E → List E
  merge [] ys = ys
  merge (x ∷ xs) ys = merge⁺ x xs ys

  merge⁺ : E → List E → List E → List E
  merge⁺ x xs [] = x ∷ xs
  merge⁺ x xs (y ∷ ys) = merge-on x xs y ys (x ≤? y)

private variable lb : ⌊∙⌋

Sorted-cons : E → (⌊∙⌋ → Type r) → ⌊∙⌋ → Type r
Sorted-cons x xs lb = (lb ≤⌊ x ⌋) × xs ⌊ x ⌋

SortedFrom : ⌊∙⌋ → List E → Type r
SortedFrom = flip (foldr Sorted-cons (const Poly.⊤))

Sorted : List E → Type r
Sorted = SortedFrom ⌊⊥⌋

mutual
  merge-sorts : ∀ xs ys → SortedFrom lb xs → SortedFrom lb ys → SortedFrom lb (merge xs ys)
  merge-sorts [] ys Sxs Sys = Sys
  merge-sorts (x ∷ xs) ys Sxs Sys = merge⁺-sorts x xs ys Sxs Sys

  merge⁺-sorts : ∀ x xs ys → SortedFrom lb (x ∷ xs) → SortedFrom lb ys → SortedFrom lb (merge⁺ x xs ys)
  merge⁺-sorts _ xs [] Sxs Sys = Sxs
  merge⁺-sorts {lb = lb} x xs (y ∷ ys) Sxs Sys = merge-on-sorts {lb = lb} x xs y ys Sxs Sys (x ≤? y)

  merge-on-sorts : ∀ x xs y ys →
                   SortedFrom lb (x ∷ xs) →
                   SortedFrom lb (y ∷ ys) →
                   (x≤?y : (x ≤ y) ⊎ (y ≤ x)) →
                   SortedFrom lb (merge-on x xs y ys x≤?y)
  merge-on-sorts x xs y ys (lb≤x , Sxs) (_    , Sys) (inl x≤y) = lb≤x , merge⁺-sorts y ys xs (x≤y , Sys) Sxs
  merge-on-sorts x xs y ys (_    , Sxs) (lb≤y , Sys) (inr y≤x) = lb≤y , merge⁺-sorts x xs ys (y≤x , Sxs) Sys

-- open import Relation.Binary.Equivalence.Reasoning (equivPerm {A = E}) public

-- mutual
--   merge-perm : ∀ xs ys → merge xs ys ↭ (xs ++ ys)
--   merge-perm [] ys _ = refl-⇔
--   merge-perm (x ∷ xs) ys = merge⁺-perm x xs ys

--   merge⁺-perm : ∀ x xs ys → merge⁺ x xs ys ↭ (x ∷ xs ++ ys)
--   merge⁺-perm x xs [] = {!!}
--   merge⁺-perm x xs (y ∷ ys) = {!!}

--   merge-on-perm : ∀ x xs y ys →
--                    (x≤?y : (x ≤ y) ⊎ (y ≤ x)) →
--                    merge-on x xs y ys x≤?y ↭ (x ∷ xs ++ y ∷ ys)
--   merge-on-perm x xs y ys (inl x≤y) = consₚ x {!merge⁺-perm !} -- lb≤x , merge⁺-sorts y ys xs (x≤y , Sys) Sxs
--   merge-on-perm x xs y ys (inr y≤x) = {!!} -- lb≤y , merge⁺-sorts x xs ys (y≤x , Sxs) Sys
\end{code}
