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

-- Definition 5: Surjections
open import Function.Surjective using (_↠!_; _↠_)

-- Theorem 1
open import Cardinality.Finite.SplitEnumerable using (ℰ!⇔Fin↠!)

-- Lemma 1
open import Cardinality.Finite.SplitEnumerable using (ℰ!⇒Discrete)
