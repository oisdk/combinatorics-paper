\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.Instances where

open import Cardinality.Finite
open import Data.Fin
open import Prelude

instance
  fin-prod : ⦃ lhs : ℰ A ⦄ ⦃ rhs : ℰ B ⦄ → ℰ (A × B)
  fin-prod ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |×| rhs

instance
  fin-sum : ⦃ lhs : ℰ A ⦄ ⦃ rhs : ℰ B ⦄ → ℰ (A ⊎ B)
  fin-sum ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |⊎| rhs

instance
  fin-fun : {A B : Type₀} ⦃ lhs : ℰ A ⦄ ⦃ rhs : ℰ B ⦄ → ℰ (A → B)
  fin-fun ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |→| rhs

instance
  fin-bool : ℰ Bool
  fin-bool = ℰ⟨Bool⟩

instance
  fin-fin : ∀ {n} → ℰ (Fin n)
  fin-fin = ℰ⟨Fin⟩ _

instance
  fin-top : ℰ ⊤
  fin-top = ℰ⟨⊤⟩

instance
  fin-bot : ℰ ⊥
  fin-bot = ℰ⟨⊥⟩

import Data.Unit.UniversePolymorphic
open import Data.List

instance
  fin-top′ : ∀{ℓ} → ℰ (Data.Unit.UniversePolymorphic.⊤ {ℓ})
  fin-top′ .fst = Data.Unit.UniversePolymorphic.tt ∷ []
  fin-top′ .snd   _ = f0 , refl
\end{code}
