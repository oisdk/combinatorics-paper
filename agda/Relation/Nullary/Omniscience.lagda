\begin{code}
{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Omniscience where

open import Prelude
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.Bool using (bool)

private
  variable
    p : Level
\end{code}
%<*omniscient>
\begin{code}
Omniscient : ∀ p {a} → Type a → Type _
Omniscient p A = ∀ {P : A → Type p} → (P? : ∀ x → Dec (P x)) → Dec (∃[ x ] P x)
\end{code}
%</omniscient>
%<*exhaustible>
\begin{code}
Exhaustible : ∀ p {a} → Type a → Type _
Exhaustible p A = ∀ {P : A → Type p} → (P? : ∀ x → Dec (P x)) → Dec (∀ x → P x)
\end{code}
%</exhaustible>
%<*weaken>
\begin{code}
Omniscient→Exhaustible : ∀ {p} → Omniscient p A → Exhaustible p A
Omniscient→Exhaustible omn P? =
  map-dec
    (λ ¬∃P x → Dec→Stable _ (P? x) (¬∃P ∘ (x ,_)))
    (λ ¬∃P ∀P → ¬∃P λ p → snd p (∀P (fst p)))
    (not (omn (not ∘ P?)))
\end{code}
%</weaken>
