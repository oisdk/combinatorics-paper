{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.ManifestBishop where

open import Prelude

import Cardinality.Finite.ManifestBishop.Inductive as 𝕃
import Cardinality.Finite.ManifestBishop.Container as ℒ

open import Cardinality.Finite.ManifestBishop.Isomorphism

open import Data.Fin

module _ where
  open ℒ
  ℬ⇔Fin≃ : ℬ A ⇔ (∃[ n ] (Fin n ≃ A))
  ℬ⇔Fin≃ .fun ((n , xs) , cov) .fst = n
  ℬ⇔Fin≃ .fun ((n , xs) , cov) .snd .fst = xs
  ℬ⇔Fin≃ .fun ((n , xs) , cov) .snd .snd .equiv-proof = cov
  ℬ⇔Fin≃ .inv (n , (xs , cov)) = ((n , xs) , cov .equiv-proof)
  ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .fst = n
  ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .snd .fst = xs
  ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .snd .snd .equiv-proof = cov .equiv-proof
  ℬ⇔Fin≃ .leftInv _ = refl

module _ where
  open 𝕃

  open import Cardinality.Finite.SplitEnumerable
  open import Cardinality.Finite.SplitEnumerable.Inductive
  open import Cardinality.Finite.SplitEnumerable.Isomorphism

  ℬ⇒ℰ! : ℬ A → ℰ! A
  ℬ⇒ℰ! xs .fst = xs .fst
  ℬ⇒ℰ! xs .snd x = xs .snd x .fst

  ℰ!⇒ℬ : ℰ! A → ℬ A
  ℰ!⇒ℬ xs = λ where
      .fst → uniques disc (xs .fst)
      .snd x → ∈⇒∈! disc x (xs .fst) (xs .snd x)
    where
    disc = ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun xs)

  open import Data.Tuple

  _|Π|_ :  ∀ {u} {A : Type₀} {U : A → Type u} →
          ℰ! A →
          ((x : A) → ℰ! (U x)) →
          ℰ! ((x : A) → U x)
  _|Π|_ xs =
    subst
      (λ t → {A : t → Type _} → ((x : t) → ℰ! (A x)) → ℰ! ((x : t) → (A x)))
      (ua (ℬ⇔Fin≃ .fun (𝕃⇔ℒ⟨ℬ⟩ .fun (ℰ!⇒ℬ xs)) .snd))
      (subst ℰ! (isoToPath Tuple⇔ΠFin) ∘ ℰ!⟨Tuple⟩)
