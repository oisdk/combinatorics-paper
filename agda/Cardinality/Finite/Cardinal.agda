{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.Cardinal where

open import Prelude
open import Cardinality.Finite.ManifestBishop
open import Cardinality.Finite.ManifestBishop.Inductive
open import Cardinality.Finite.ManifestBishop.Isomorphism
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Isomorphism

open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

open import Relation.Nullary.Discrete.Properties

open import Data.Fin

𝒞 : Type a → Type a
𝒞 A = ∥ ℬ A ∥

_∥×∥_ : 𝒞 A → 𝒞 B → 𝒞 (A × B)
xs ∥×∥ ys = do
  x ← xs
  y ← ys
  ∣ ℰ!⇒ℬ (ℬ⇒ℰ! x |×| ℬ⇒ℰ! y) ∣

_∥⊎∥_ : 𝒞 A → 𝒞 B → 𝒞 (A ⊎ B)
xs ∥⊎∥ ys = do
  x ← xs
  y ← ys
  ∣ ℰ!⇒ℬ (ℬ⇒ℰ! x |⊎| ℬ⇒ℰ! y) ∣

_∥→∥_ : {A : Type₀} → 𝒞 A → 𝒞 B → 𝒞 (A → B)
xs ∥→∥ ys = do
  x ← xs
  y ← ys
  ∣ ℰ!⇒ℬ (ℬ⇒ℰ! x |Π| const (ℬ⇒ℰ! y)) ∣

𝒞⇒Discrete : 𝒞 A → Discrete A
𝒞⇒Discrete = recPropTrunc isPropDiscrete (ℰ!⇒Discrete ∘ 𝕃⇔ℒ⟨ℰ!⟩ .fun ∘ ℬ⇒ℰ!)

open import Data.Sigma.Properties
open import Data.Fin.Properties using (Fin-inj)
open import Data.Nat.Properties using (isSetℕ)
open import Cubical.Foundations.HLevels

cardinality : ∥ ∃[ n ] (Fin n ≃ A) ∥ → ∃[ n ] ∥ Fin n ≃ A ∥
cardinality {A = A} = recPropTrunc→Set (isOfHLevelΣ 2 isSetℕ λ _ → isProp→isSet squash) alg const-alg
  where
  alg : Σ[ n ⦂ ℕ ] (Fin n ≃ A) → Σ[ n ⦂ ℕ ] ∥ Fin n ≃ A ∥
  alg (n , f≃A) = n , ∣ f≃A ∣

  const-alg : (x y : ∃[ n ] (Fin n ≃ A)) → alg x ≡ alg y
  const-alg (n , x) (m , y) =
    ΣProp≡
      (λ _ → squash)
      {n , ∣ x ∣} {m , ∣ y ∣}
      (Fin-inj n m (ua (x ⟨ trans-≃ ⟩ (sym-≃ y))))

open import Relation.Binary
open import Data.List.Relation.Binary.Permutation

perm-ℬ : (xs ys : ℬ A) → xs .fst ↭ ys .fst
perm-ℬ xs ys  x .fun  _    = ys  .snd x .fst
perm-ℬ xs ys  x .inv  _    = xs  .snd x .fst
perm-ℬ xs ys  x .rightInv  = ys  .snd x .snd
perm-ℬ xs ys  x .leftInv   = xs  .snd x .snd

module _ {e r} {E : Type e} (totalOrder : TotalOrder E r) where
  open import Data.List.Sort totalOrder
  open import Cubical.HITs.PropositionalTruncation using (recPropTrunc→Set)
  open import Data.Sigma.Properties
  open import Cardinality.Finite.ManifestBishop using (ℰ!⇒ℬ)
  open import Cardinality.Finite.ManifestEnumerable.Inductive
  open import Cardinality.Finite.ManifestEnumerable

  𝒞⇒ℬ : 𝒞 E → ℬ E
  𝒞⇒ℬ xs = (ℰ!⇒ℬ ∘ ℰ⇒ℰ! discreteE ∘ recPropTrunc→Set (isSet⟨ℰ⟩ (Discrete→isSet discreteE)) alg const-alg) xs
    where
    discreteE = 𝒞⇒Discrete xs

    alg : ℬ E → ℰ E
    alg xs .fst = sort (xs .fst)
    alg xs .snd x = ∣ sort-perm (xs .fst) x .inv (xs .snd x .fst) ∣

    const-alg : (xs ys : ℬ E) → alg xs ≡ alg ys
    const-alg xs ys =
      ΣProp≡
        (λ _ → hLevelPi 1 (λ _ → squash))
        (perm-invar (xs .fst) (ys .fst) (perm-ℬ xs ys))
