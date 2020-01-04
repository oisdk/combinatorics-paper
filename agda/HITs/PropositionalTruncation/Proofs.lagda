\begin{code}
{-# OPTIONS --cubical --safe #-}

module HITs.PropositionalTruncation.Proofs where

open import Cubical.HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar
open import Cubical.Foundations.Prelude
open import Level
open import Data.Empty

\end{code}
%<*rec>
\begin{code}
rec : isProp B → (A → B) → ∥ A ∥ → B
rec isPropB f ∣ x ∣ = f x
rec isPropB f (squash xs ys i) =
  isPropB (rec isPropB f xs) (rec isPropB f ys) i
\end{code}
%</rec>
%<*doubleNeg>
\begin{code}
refute : ∥ A ∥ → (A → ⊥) → ⊥
refute = rec (λ f g i x → isProp⊥ (f x) (g x) i) (λ x f → f x)
\end{code}
%</doubleNeg>
\begin{code}
closed : ∥ (A → B) ∥ → A → ∥ B ∥
closed fs x = (λ f → f x) ∥$∥ fs
\end{code}
