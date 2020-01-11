{-# OPTIONS --cubical --safe #-}

module README where

--------------------------------------------------------------------------------
-- Section 2: Split Enumerability
--------------------------------------------------------------------------------

-- Definition 1: Container
open import Container using (Container; ⟦_⟧)

-- Definition 2: List
open import Container.List using (List)

-- Definition 3: Fin
open import Data.Fin.Base using (Fin)

-- Definition 4: ℰ!
open import Cardinality.Finite.SplitEnumerable.Container using (ℰ!)

-- Container based definition is isomophic to inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism using (𝕃⇔ℒ⟨ℰ!⟩)

-- Definition 5: Surjections
open import Function.Surjective using (_↠!_; _↠_)

-- Theorem 1
open import Cardinality.Finite.SplitEnumerable using (ℰ!⇔Fin↠!)

-- Lemma 1
open import Cardinality.Finite.SplitEnumerable using (ℰ!⇒Discrete)

-- Lemma 2
open import Cardinality.Finite.SplitEnumerable using (ℰ!⟨2⟩; ℰ!⟨⊤⟩; ℰ!⟨⊥⟩)

-- Theorem 2
open import Cardinality.Finite.SplitEnumerable using (_|Σ|_)

--------------------------------------------------------------------------------
-- Section 3: Manifest Bishop Finiteness
--------------------------------------------------------------------------------

-- Definition 6: Manifest Bishop Finiteness
open import Cardinality.Finite.ManifestBishop.Container using (ℬ)

-- Defintion 7: Unique Membership
open import Container.Membership using (_∈!_)

-- Container based definition is isomophic to inductive
open import Cardinality.Finite.ManifestBishop.Isomorphism using (𝕃⇔ℒ⟨ℬ⟩)

-- Lemma 3
open import Cardinality.Finite.ManifestBishop using (ℬ⇔Fin≃)

-- Theorem 3
open import Cardinality.Finite.ManifestBishop using (ℰ!⇒ℬ)

-- Theorem 4
open import Cardinality.Finite.ManifestBishop using (_|Π|_)

--------------------------------------------------------------------------------
-- Section 4: Manifest Enumerability
--------------------------------------------------------------------------------

-- Definition 8: Manifest Bishop Finiteness
open import Cardinality.Finite.ManifestEnumerable.Container using (ℰ)

-- Definition 9: Propositional Truncation (from the cubical agda library)
open import Cubical.HITs.PropositionalTruncation using (∥_∥)

-- Theorem 5
open import Cardinality.Finite.ManifestEnumerable using (ℰ⟨S¹⟩)

-- Lemma 4
open import Cardinality.Finite.ManifestEnumerable using (ℰ⇔Fin↠)

-- Theorem 6
open import Cardinality.Finite.ManifestEnumerable using (ℰ⇒ℰ!)

-- Lemma 5
open import Cardinality.Finite.ManifestEnumerable using (_∥Σ∥_)

--------------------------------------------------------------------------------
-- Section 5: Cardinal Finiteness
--------------------------------------------------------------------------------
