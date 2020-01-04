\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Properties where

open import Prelude
open import Cubical.Foundations.HLevels using (ΣProp≡) public
-- Σ≡-Prop : {A : Type a} {B : A → Type b}
--         → (xs ys : Σ A B)
--         → (isProp (B (xs .fst)))
--         → fst xs ≡ fst ys
--         → xs ≡ ys
-- Σ≡-Prop {A = A} {B = B} xs ys isPropB xs≡ys =
--   subst
--     (λ fst → (snd : B fst) → xs ≡ (fst , snd))
--     xs≡ys
--     (λ ys₂ i → (xs .fst) , isPropB (xs .snd) ys₂ i)
--     (ys .snd)
\end{code}
