\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module HLevels.Proposition where

open import Cubical.HITs.PropositionalTruncation
open import Function.Isomorphism
open import Level
open import HLevels
open import Function.Biconditional
open import Function

prop-untrunc : isProp A → A ⇔ ∥ A ∥
prop-untrunc isPropA .fun = ∣_∣
prop-untrunc isPropA .inv = recPropTrunc isPropA λ x → x
prop-untrunc isPropA .rightInv _ = squash _ _
prop-untrunc isPropA .leftInv _ = isPropA _ _
\end{code}
%<*prop-iff>
\begin{code}
prop-iff : isProp A → isProp B → A ↔ B → A ⇔ B
prop-iff isPropA isPropB A↔B .fun = A↔B .fun
prop-iff isPropA isPropB A↔B .inv = A↔B .inv
prop-iff isPropA isPropB A↔B .leftInv  x = isPropA _ x
prop-iff isPropA isPropB A↔B .rightInv x = isPropB _ x
\end{code}
%</prop-iff>
\begin{code}
prop-trunc-iff : A ↔ B → ∥ A ∥ ⇔ ∥ B ∥
prop-trunc-iff A↔B = prop-iff squash squash
  λ where .fun → recPropTrunc squash (∣_∣ ∘ A↔B .fun)
          .inv → recPropTrunc squash (∣_∣ ∘ A↔B .inv)
\end{code}
