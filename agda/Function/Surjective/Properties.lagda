\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Function.Surjective.Properties where

open import Path
open import Function.Fiber
open import Level
open import HITs.PropositionalTruncation
open import Data.Sigma
open import Function.Surjective.Base
open import Function.Injective.Base
open import Function.Injective.Properties
open import Path.Reasoning
open import Relation.Nullary.Discrete
open import Function

A↠!B⇒B↣A : A ↠! B → B ↣ A
A↠!B⇒B↣A (f , surj) .fst x = surj x .fst
A↠!B⇒B↣A (f , surj) .snd x y f⁻¹⟨x⟩≡f⁻¹⟨y⟩ =
  x                ≡˘⟨ surj x .snd ⟩
  f (surj x .fst)  ≡⟨ cong f f⁻¹⟨x⟩≡f⁻¹⟨y⟩ ⟩
  f (surj y .fst)  ≡⟨ surj y .snd ⟩
  y ∎

Discrete↠!A⇒Discrete⟨A⟩ : A ↠! B → Discrete A → Discrete B
Discrete↠!A⇒Discrete⟨A⟩ A↠!B =
  A↣Discrete⇒Discrete⟨A⟩ (A↠!B⇒B↣A A↠!B)

SplitSurjective⟨id⟩ : SplitSurjective (id {A = A})
SplitSurjective⟨id⟩ x .fst = x
SplitSurjective⟨id⟩ x .snd _ = x
\end{code}
%<*split-surj-ident>
\begin{code}
↠!-ident : A ↠! A
↠!-ident .fst = id
↠!-ident .snd y .fst = y
↠!-ident .snd y .snd _ = y
\end{code}
%</split-surj-ident>
\begin{code}
↠!-comp : A ↠! B → B ↠! C → A ↠! C
↠!-comp a→b b→c .fst = b→c .fst ∘ a→b .fst
↠!-comp a→b b→c .snd y .fst = a→b .snd (b→c .snd y .fst) .fst
↠!-comp a→b b→c .snd y .snd = cong (fst b→c) (snd (snd a→b (fst (snd b→c y)))) ; snd (snd b→c y)
\end{code}
