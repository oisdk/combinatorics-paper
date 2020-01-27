{-# OPTIONS --cubical --safe #-}

module README where

--------------------------------------------------------------------------------
-- Section 1: Introduction
--------------------------------------------------------------------------------

-- 0, 1, and 2 types
import Data.Empty using (⊥)
import Data.Unit  using (⊤)
import Data.Bool  using (Bool)

-- Dependent Sum and Product
import Data.Sigma using (Σ)
import Data.Pi    using (Π)

-- Disjoint Union
import Data.Sum using (_⊎_)
import Data.Sum.Properties using (sumAsSigma)

-- Definition 1: Path types
import Path using (_≡_)

-- Definition 2: Homotopy Levels
import HLevels using (isContr; isProp; isSet)

-- Definition 3: Fibres
import Function.Fiber using (fiber)

-- Definition 4: Equivalences
import Equiv using (isEquiv; _≃_)

-- Definition 5: Decidable
import Relation.Nullary.Decidable using (Dec)

-- Definition 6: Discrete
import Relation.Nullary.Discrete using (Discrete)
import Relation.Nullary.Discrete.Properties using (Discrete→isSet)

-- Definition 8: Propositional Truncation
import HITs.PropositionalTruncation using (∥_∥)
import HITs.PropositionalTruncation using (recPropTrunc; recPropTrunc→Set)

--------------------------------------------------------------------------------
-- Section 2: Finiteness Predicates
--------------------------------------------------------------------------------

-- Definition 9: Split Enumerability
import Cardinality.Finite.SplitEnumerable.Container using (ℰ!)

-- Container based definition is isomophic to inductive
import Cardinality.Finite.SplitEnumerable.Isomorphism using (𝕃⇔ℒ⟨ℰ!⟩)

-- Definition 10: Container
import Container using (Container; ⟦_⟧)

-- Definition 11: List
import Container.List using (List)

-- Definition 12: Fin
import Data.Fin.Base using (Fin)

-- Definition 13: Surjections
import Function.Surjective using (_↠!_; _↠_)

-- Lemma 1
import Cardinality.Finite.SplitEnumerable using (ℰ!⇔Fin↠!)

-- Lemma 2
import Function.Surjective.Properties using (Discrete↠!A⇒Discrete⟨A⟩)

-- Lemma 3
import Cardinality.Finite.SplitEnumerable using (ℰ!⇒Discrete)

-- Definition 14: Manifest Bishop Finiteness
import Cardinality.Finite.ManifestBishop.Container using (ℬ)

-- Container based definition is isomophic to inductive
import Cardinality.Finite.ManifestBishop.Isomorphism using (𝕃⇔ℒ⟨ℬ⟩)

-- Definition 15: Unique Membership
import Container.Membership using (_∈!_)

-- Lemma 4
import Cardinality.Finite.ManifestBishop using (ℬ⇔Fin≃)

-- Definition 16: Cardinal Finiteness
import Cardinality.Finite.Cardinal using (𝒞; 𝒞≃Fin≃)

-- Lemma 5
import Cardinality.Finite.Cardinal using (cardinality)

-- Lemma 6
import Cardinality.Finite.Cardinal using (𝒞⇒Discrete)

-- Definition 17: Manifest Enumerability
import Cardinality.Finite.ManifestEnumerable.Container using (ℰ)

-- Container based definition is isomorphic to inductive
import Cardinality.Finite.ManifestEnumerable.Isomorphism using (𝕃⇔ℒ⟨ℰ⟩)

-- Lemma 7
import Cardinality.Finite.ManifestEnumerable using (ℰ⇔Fin↠)

-- Definition 18: S¹
open import Cubical.HITs.S1 using (S¹)

-- Lemma 8
import Cardinality.Finite.ManifestEnumerable using (ℰ⟨S¹⟩)

-- Definition 19: Kuratowski finite subset
import Algebra.Construct.Free.Semilattice using (𝒦)

-- Definition 20: Membership of 𝒦
import Algebra.Construct.Free.Semilattice.Relation.Unary using (_∈_)

-- Definition 21: Kuratowski finiteness
import Cardinality.Finite.Kuratowski using (𝒦ᶠ)

-- Lemma 9
import Cardinality.Finite.Kuratowski using (isProp𝒦ᶠ)

-- Lemma 10
import Cardinality.Finite.Kuratowski using (𝒦ᶠ⟨S¹⟩)

--------------------------------------------------------------------------------
-- Section 5: Cardinal Finiteness
--------------------------------------------------------------------------------

-- -- Theorem 6
-- import Cardinality.Finite.ManifestEnumerable using (ℰ⇒ℰ!)

-- -- Lemma 5
-- import Cardinality.Finite.ManifestEnumerable using (_∥Σ∥_)



-- -- Lemma 6
-- import Cardinality.Finite.Cardinal using (_∥×∥_; _∥⊎∥_; _∥→∥_)


-- -- Theorem 9
-- import Cardinality.Finite.Cardinal using (𝒞⇒ℬ)

-- -- Definition 11
-- import Data.List.Relation.Binary.Permutation using (_↭_)

-- -- Lemma 7
-- import Data.List.Sort using (perm-invar)

-- --------------------------------------------------------------------------------
-- -- Section 6: Kuratowski Finiteness
-- --------------------------------------------------------------------------------

-- -- Definition 12: Kuratowski-finite set



-- -- Theorem 10
-- import Cardinality.Finite.Kuratowski using (∥ℰ∥⇔𝒦)

-- --------------------------------------------------------------------------------
-- -- Section 7: Infinite Cardinalities
-- --------------------------------------------------------------------------------

-- -- Definition 15: Stream
-- import Codata.Stream using (Stream)

-- -- Definition 16: Split Countability
-- import Cardinality.Infinite.Split using (ℰ!)

-- -- Theorem 11
-- import Cardinality.Infinite.Split using (_|Σ|_)

-- -- Theorem 12
-- import Cardinality.Infinite.Split using (star)

-- --------------------------------------------------------------------------------
-- -- Section 8: Practical Uses
-- --------------------------------------------------------------------------------

-- -- Definition 17: Limited Principle of Omniscience
-- import Relation.Nullary.Omniscience using (Omniscient)

-- -- Definition 18: Exhaustibility
-- import Relation.Nullary.Omniscience using (Exhaustible)

-- -- Theorem 13
-- import Cardinality.Finite.Kuratowski using (𝒦ᶠ⇒Exhaustible)

-- -- Theorem 14
-- import Cardinality.Finite.ManifestEnumerable using (ℰ⇒Omniscient)

-- -- Theorem 15
-- import Cardinality.Finite.Kuratowski using (𝒦ᶠ⇒∣Omniscient∣)

-- -- Automated proofs
-- import Data.Pauli

-- -- Lemma 2
-- import Cardinality.Finite.SplitEnumerable using (ℰ!⟨2⟩; ℰ!⟨⊤⟩; ℰ!⟨⊥⟩)

-- -- Theorem 2
-- import Cardinality.Finite.SplitEnumerable using (_|Σ|_)

-- -- Theorem 3
-- import Cardinality.Finite.ManifestBishop using (ℰ!⇒ℬ)

-- -- Theorem 4
-- import Cardinality.Finite.ManifestBishop using (_|Π|_)
