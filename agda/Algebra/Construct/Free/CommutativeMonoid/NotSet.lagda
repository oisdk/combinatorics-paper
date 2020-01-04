\begin{code}
{-# OPTIONS --cubical --safe #-}
module Algebra.Construct.Free.CommutativeMonoid.NotSet where

open import Prelude
open import Algebra
open import Path.Reasoning
\end{code}
%<*definition>
\begin{code}
infixr 5 _∷_
data ⟅_⟆ (A : Type a) : Type a where
  []   : ⟅ A ⟆
  _∷_  : A → ⟅ A ⟆ → ⟅ A ⟆
  com  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
\end{code}
%</definition>
\begin{code}
module _ {ℓ} (mon : CommutativeMonoid ℓ) where
 open CommutativeMonoid mon
\end{code}
%<*hom>
\begin{code}
 ⟦_⟧ : (A → 𝑆) → ⟅ A ⟆ → 𝑆
 ⟦ h ⟧ [] = ε
 ⟦ h ⟧ (x ∷ xs) = h x ∙ ⟦ h ⟧ xs
 ⟦ h ⟧ (com x y xs i) = begin[ i ]
   h x ∙ (h y ∙ ⟦ h ⟧ xs)
                         ≡˘⟨ assoc _ _ _ ⟩
   (h x ∙ h y) ∙ ⟦ h ⟧ xs
                         ≡⟨ cong (_∙ ⟦ h ⟧ xs)
                             (comm _ _) ⟩
   (h y ∙ h x) ∙ ⟦ h ⟧ xs
                         ≡⟨ assoc _ _ _ ⟩
   h y ∙ (h x ∙ ⟦ h ⟧ xs) ∎
\end{code}
%</hom>
