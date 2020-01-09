{-# OPTIONS --cubical --safe #-}

module Data.Pauli where

open import Prelude hiding (I)
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Search
open import Cardinality.Finite.SplitEnumerable.Instances
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Data.Fin

data Pauli : Type₀ where X Y Z I : Pauli

instance
  ℰ!⟨Pauli⟩ : ℰ! Pauli
  ℰ!⟨Pauli⟩ .fst  = X ∷ Y ∷ Z ∷ I ∷ []
  ℰ!⟨Pauli⟩ .snd X  = f0 , refl
  ℰ!⟨Pauli⟩ .snd Y  = fs f0 , refl
  ℰ!⟨Pauli⟩ .snd Z  = fs (fs f0) , refl
  ℰ!⟨Pauli⟩ .snd I  = fs (fs (fs f0)) , refl

infix 4 _≟_
_≟_ : (x y : Pauli) → Dec (x ≡ y)
_≟_ = ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun ℰ!⟨Pauli⟩)

infixl 6 _·_
_·_ : Pauli → Pauli → Pauli
I  · x  = x
X  · X  = I
X  · Y  = Z
X  · Z  = Y
X  · I  = X
Y  · X  = Z
Y  · Y  = I
Y  · Z  = X
Y  · I  = Y
Z  · X  = Y
Z  · Y  = X
Z  · Z  = I
Z  · I  = Z

cancel-· : ∀ x → x · x ≡ I
cancel-· = ∀↯ⁿ 1 λ x → x · x ≟ I

comm-· : ∀ x y → x · y ≡ y · x
comm-· = ∀↯ⁿ 2 λ x y → x · y ≟ y · x

assoc-· : ∀ x y z → (x · y) · z ≡ x · (y · z)
assoc-· = ∀↯ⁿ 3 λ x y z → (x · y) · z ≟ x · (y · z)
