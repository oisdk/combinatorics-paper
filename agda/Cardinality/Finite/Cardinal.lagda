\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.Cardinal where

open import Prelude
open import Cardinality.Finite.ManifestBishop
open import Cardinality.Finite.SplitEnumerable
open import HITs.PropositionalTruncation.Sugar
open import Relation.Nullary
open import Data.List.Relation.Unary
open import Cubical.HITs.PropositionalTruncation
open import Relation.Nullary.Decidable
open import Data.Fin
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma.Properties using (Σ≡; ΣPathP)
open import Cubical.Foundations.Everything using (J)
open import Data.Nat using (discreteℕ)

𝒞 : Type a → Type a
𝒞 A = ∥ ℬ A ∥

𝒞⇔Fin≃ : {A : Type₀} → 𝒞 A ⇔ ∥ ∃[ n ] Fin n ≃ A ∥
𝒞⇔Fin≃ = prop-trunc-iff λ where
  .fun B → _ , ℬ⇒Fin≃ B
  .inv (n , f≃A) → subst ℬ (ua f≃A) (ℰ!⇒ℬ (ℰ!⟨Fin⟩ n))

isPropDiscrete : isProp (Discrete A)
isPropDiscrete _≟₁_ _≟₂_ i x y = isPropDec (Discrete→isSet _≟₁_ x y) (x ≟₁ y) (x ≟₂ y) i

𝒞⇒Discrete : 𝒞 A → Discrete A
𝒞⇒Discrete = recPropTrunc isPropDiscrete ℬ⇒Discrete

open import Data.Fin.Properties
open import Cubical.Foundations.HLevels

isSetCard : isSet (∃[ n ] ∥ Fin n ≃ A ∥)
isSetCard = isOfHLevelΣ 2 (Discrete→isSet discreteℕ) λ _ → isProp→isSet squash

rec→Set = recPropTrunc→Set
open import Cubical.Foundations.Function using (2-Constant)
open import Data.Sigma.Properties

cardinality : ∥ ∃[ n ] Fin n ≃ A ∥ → ∃[ n ] ∥ Fin n ≃ A ∥
cardinality {A = A} = rec→Set isSetCard alg const-alg
  where
\end{code}
%<*trunc-alg>
\begin{code}
  alg : ∃[ n ] Fin n ≃ A → ∃[ n ] ∥ Fin n ≃ A ∥
  alg (n , f≃A) = n , ∣ f≃A ∣
\end{code}
%</trunc-alg>
%<*const-alg>
\begin{code}
  const-alg : (x y : ∃[ n ] Fin n ≃ A) → alg x ≡ alg y
  const-alg (n , x) (m , y) =
    ΣProp≡
      (λ _ → squash)
      {n , ∣ x ∣} {m , ∣ y ∣}
      (Fin-inj n m (ua (compEquiv x (invEquiv y))))
\end{code}
%</const-alg>
\begin{code}
prop-dec : ∥ Dec A ∥ → Dec ∥ A ∥
prop-dec = recPropTrunc (isPropDec squash) (map-dec ∣_∣ refute-trunc)

module CardinalQuant {a} {A : Type a} {p} {P : A → Type p} where
  open Forall P
  open Exists P
  open Quantifications using (for-some; for-each) renaming (∀? to ∀?!; ∃? to ∃?!)

  ∀? : 𝒞 A → (∀ x → Dec (P x)) → Dec (∀ x → P x)
  ∀? C P? = map-dec (λ ∀Px x → recompute (P? x) (∀Px x)) (λ ¬∥∀∥ ∀Px → ¬∥∀∥ (λ x → ∣ ∀Px x ∣)) ∥∀?∥
    where
    ∥P?∥ : ∀ x → Dec ∥ P x ∥
    ∥P?∥ = map-dec ∣_∣ refute-trunc ∘ P?

    ∥∀?∥ : Dec (∀ x → ∥ P x ∥)
    ∥∀?∥ = recPropTrunc (isPropDec λ p q i x → squash (p x) (q x) i) (λ B → ∀?! (ℬ⇒ℰ! B) ∥P?∥) C

  ∥∃?∥ : 𝒞 A → (∀ x → Dec (P x)) → Dec ∥ ∃[ x ] (P x) ∥
  ∥∃?∥ C P? = prop-dec ((λ B → ∃?! (ℬ⇒ℰ! B) P?) ∥$∥ C)

  ∃? : (∀ x y → P x → P y → x ≡ y) →
       𝒞 A →
       (∀ x → Dec (P x)) →
       Dec (∃[ x ] P x)
  ∃? uniq C P? = map-dec elim∃ (λ ¬∥∃∥ ∃Px → ¬∥∃∥ ∣ ∃Px ∣) (∥∃?∥ C P?)
    where
    isProp∃ : isProp (∃[ x ] ∥ P x ∥)
    isProp∃ (x , Px) (y , Py) =
      subst
        (λ z → (Pz : ∥ P z ∥) → (x , Px) ≡ (z , Pz))
        (uniq x y (recompute (P? x) Px) (recompute (P? y) Py))
        (λ Pz i → x , squash Px Pz i)
        Py

    elim∃ : ∥ ∃[ x ] (P x) ∥ → ∃[ x ] P x
    elim∃ = map₂ (recompute (P? _)) ∘ recPropTrunc isProp∃ (map₂ ∣_∣)


open import Cubical.Foundations.HLevels using (isOfHLevelΣ; hLevelPi)
open import Data.List.Relation.Binary using (isOfHLevelList)
open import Data.List using (_!_)
open import Relation.Binary
open import Cardinality.Finite.ManifestEnumerable
open import Data.List.Membership
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
\end{code}
