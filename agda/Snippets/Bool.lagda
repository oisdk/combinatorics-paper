\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Bool where

open import Data.Bool
open import Prelude hiding (_∧_)

\end{code}
%<*and-def>
\begin{code}
_∧_ : Bool → Bool → Bool
false  ∧ false  = false
false  ∧ true   = false
true   ∧ false  = false
true   ∧ true   = true
\end{code}
%</and-def>
\begin{code}
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Search
open import Cardinality.Finite.SplitEnumerable.Instances
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Cardinality.Finite.ManifestBishop
open import Data.Bool.Properties using (discreteBool)

infixl 4 _≟_
_≟_ = discreteBool
\end{code}
%<*bool-assoc-auto-proof>
\begin{code}
∧-assoc : ∀ x y z → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-assoc = ∀↯ⁿ 3 λ x y z → (x ∧ y) ∧ z ≟ x ∧ (y ∧ z)
\end{code}
%</bool-assoc-auto-proof>
%<*some-assoc>
\begin{code}
some-assoc : Σ[ f ⦂ (Bool → Bool → Bool) ] ∀ x y z → f (f x y) z ≡ f x (f y z)
some-assoc = ∃↯ⁿ 1 λ f → ∀?ⁿ 3 λ x y z → f (f x y) z ≟ f x (f y z)
\end{code}
%</some-assoc>
