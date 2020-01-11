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

-- Definition 10: Cardinal Finiteness
open import Cardinality.Finite.Cardinal using (𝒞)

-- Lemma 6
open import Cardinality.Finite.Cardinal using (_∥×∥_; _∥⊎∥_; _∥→∥_)

-- Theorem 7
open import Cardinality.Finite.Cardinal using (𝒞⇒Discrete)

-- Theorem 8
open import Cardinality.Finite.Cardinal using (cardinality)

-- Theorem 9
open import Cardinality.Finite.Cardinal using (𝒞⇒ℬ)

-- Definition 11
open import Data.List.Relation.Binary.Permutation using (_↭_)

-- Lemma 7
open import Data.List.Sort using (perm-invar)

--------------------------------------------------------------------------------
-- Section 6: Kuratowski Finiteness
--------------------------------------------------------------------------------

-- Definition 12: Kuratowski-finite set
open import Algebra.Construct.Free.Semilattice using (𝒦)

-- Definition 13: Membership of 𝒦
open import Algebra.Construct.Free.Semilattice.Relation.Unary using (_∈_)

-- Definition 14: Kuratowski finiteness
open import Cardinality.Finite.Kuratowski using (𝒦ᶠ)

-- Theorem 10
open import Cardinality.Finite.Kuratowski using (∥ℰ∥⇔𝒦)

--------------------------------------------------------------------------------
-- Section 7: Infinite Cardinalities
--------------------------------------------------------------------------------

-- Definition 15: Stream
open import Codata.Stream using (Stream)

-- Definition 16: Split Countability
open import Cardinality.Infinite.Split using (ℰ!)

-- Theorem 11
open import Cardinality.Infinite.Split using (_|Σ|_)

-- Theorem 12
open import Cardinality.Infinite.Split using (star)

--------------------------------------------------------------------------------
-- Section 8: Practical Uses
--------------------------------------------------------------------------------

-- Definition 17: Limited Principle of Omniscience
open import Relation.Nullary.Omniscience using (Omniscient)

-- Definition 18: Exhaustibility
open import Relation.Nullary.Omniscience using (Exhaustible)

-- Theorem 13
open import Cardinality.Finite.Kuratowski using (𝒦ᶠ⇒Exhaustible)

-- Theorem 14
open import Cardinality.Finite.ManifestEnumerable using (ℰ⇒Omniscient)

-- Theorem 15
open import Cardinality.Finite.Kuratowski using (𝒦ᶠ⇒∣Omniscient∣)

-- Automated proofs
open import Data.Pauli
