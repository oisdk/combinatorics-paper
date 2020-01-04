\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}
module Relation.Nullary.Decidable where

open import Relation.Nullary
open import Prelude
open import Data.Bool hiding (not)
open import Data.Sum

infixl 7 _&&_
_&&_ : Dec A → Dec B → Dec (A × B)
(x && y) .does = x .does ∧ y .does
(yes x && yes y) .why  = ofʸ (x , y)
(yes x && no  y) .why  = ofⁿ (y ∘ snd)
(no  x && y) .why  = ofⁿ (x ∘ fst)

infixl 6 _||_
_||_ : Dec A → Dec B → Dec (A ⊎ B)
(x || y) .does = x .does ∨ y .does
(yes x || y) .why = ofʸ (inl x)
(no  x || yes y) .why = ofʸ (inr y)
(no  x || no  y) .why = ofⁿ (either x y)

not : Dec A → Dec (¬ A)
not x .does = Data.Bool.not (x .does)
not (yes x) .why = ofⁿ (λ z → z x)
not (no  x) .why = ofʸ x

Dec⇔⊎¬ : Dec A ⇔ A ⊎ (¬ A)
Dec⇔⊎¬ .fun (yes p) = inl p
Dec⇔⊎¬ .fun (no ¬p) = inr ¬p
Dec⇔⊎¬ .inv (inl p) = yes p
Dec⇔⊎¬ .inv (inr ¬p) = no ¬p
Dec⇔⊎¬ .rightInv (inl p) = refl
Dec⇔⊎¬ .rightInv (inr ¬p) = refl
Dec⇔⊎¬ .leftInv (yes p) = refl
Dec⇔⊎¬ .leftInv (no ¬p) = refl

open import Cubical.Data.Sum.Properties using (isOfHLevelSum)

isSetDec : isSet A → isSet (Dec A)
isSetDec isSetA = subst isSet (sym (isoToPath Dec⇔⊎¬)) (isOfHLevelSum 0 isSetA (isProp→isSet λ x y → funExt λ _ → isProp⊥ _ _))

\end{code}
