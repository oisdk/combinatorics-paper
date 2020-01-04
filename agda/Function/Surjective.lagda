\begin{code}
{-# OPTIONS --cubical --safe #-}

module Function.Surjective where

open import HLevels
open import Path
open import Path.Reasoning
open import Level
open import Function
open import Cubical.Foundations.Isomorphism using (retract) public
open import Relation.Nullary
open import Data.Product
open import Cubical.Foundations.Equiv using (fiber)
open import Function.Injective
\end{code}
%<*surj-def>
\begin{code}
Surjective : (A → B) → Type _
Surjective f = ∀ y → ∥ fiber f y ∥
\end{code}
%</surj-def>
%<*split-surj-def>
\begin{code}
SplitSurjective : (A → B) → Type _
SplitSurjective f = ∀ y → fiber f y
\end{code}
%</split-surj-def>
\begin{code}
infixr 0 _↠!_ _↠_
\end{code}
%<*surjection>
\begin{code}
_↠!_ : Type a → Type b → Type (a ℓ⊔ b)
A ↠! B = Σ (A → B) SplitSurjective
\end{code}
%</surjection>
\begin{code}
_↠_ : Type a → Type b → Type (a ℓ⊔ b)
A ↠ B = Σ (A → B) Surjective


retract⇒Surjective : ∀ (f : A → B) → (g : B → A) → retract g f → SplitSurjective f
retract⇒Surjective f g s y = g y , s y
\end{code}
%<*surj-to-inj>
\begin{code}
A↠!B⇒B↣A : A ↠! B → B ↣ A
A↠!B⇒B↣A (f , surj) .fst x = surj x .fst
A↠!B⇒B↣A (f , surj) .snd x y f⁻¹⟨x⟩≡f⁻¹⟨y⟩ =
  x                ≡˘⟨ surj x .snd ⟩
  f (surj x .fst)  ≡⟨ cong f f⁻¹⟨x⟩≡f⁻¹⟨y⟩ ⟩
  f (surj y .fst)  ≡⟨ surj y .snd ⟩
  y ∎
\end{code}
%</surj-to-inj>
%<*discrete>
\begin{code}
Discrete↠!A⇒Discrete⟨A⟩ : A ↠! B → Discrete A → Discrete B
Discrete↠!A⇒Discrete⟨A⟩ A↠!B =
  A↣Discrete⇒Discrete⟨A⟩ (A↠!B⇒B↣A A↠!B)
\end{code}
%</discrete>
\begin{code}
open import Cubical.Core.Everything using (_≃_; equiv-proof)

equiv⇒surj : A ≃ B → A ↠! B
equiv⇒surj A≃B .fst = A≃B .fst
equiv⇒surj A≃B .snd x = A≃B .snd .equiv-proof x .fst

trans↠! : (A ↠! B) → (B ↠! C) → A ↠! C
trans↠! A↠!B B↠!C .fst = B↠!C .fst ∘ A↠!B .fst
trans↠! A↠!B B↠!C .snd z =
  let y , q = B↠!C .snd z
      x , p = A↠!B .snd y
  in x , cong (B↠!C .fst) p ; q
\end{code}
