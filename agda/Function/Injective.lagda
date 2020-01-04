\begin{code}
{-# OPTIONS --cubical --safe #-}

module Function.Injective where

open import Path
open import Level
open import Function
open import Cubical.Foundations.Isomorphism using (section) public
open import Relation.Nullary
open import Data.Product
\end{code}
%<*injective-def>
\begin{code}
Injective : (A → B) → Type _
Injective f = ∀ x y → f x ≡ f y → x ≡ y
\end{code}
%</injective-def>
\begin{code}
section⇒Injective : ∀ (f : A → B) → (g : B → A) → section g f → Injective f
section⇒Injective f g s x y fx≡fy = sym (s x) ; cong g fx≡fy ; s y

infixr 0 _↣_
\end{code}
%<*injection-def>
\begin{code}
_↣_ : Set a → Set b → Set (a ℓ⊔ b)
A ↣ B = Σ[ f ∈ (A → B) ] (Injective f)
\end{code}
%</injection-def>
%<*discrete>
\begin{code}
A↣Discrete⇒Discrete⟨A⟩ : A ↣ B → Discrete B → Discrete A
A↣Discrete⇒Discrete⟨A⟩ (f , inj) _≟_ x y = ⟦yes inj x y ,no cong f ⟧ (f x ≟ f y)
\end{code}
%</discrete>
\begin{code}
open import Cubical.Foundations.Everything
open import Cubical.Core.Everything

equiv⇒Injective : A ≃ B → A ↣ B
equiv⇒Injective A≃B .fst = A≃B .fst
equiv⇒Injective A≃B .snd x y fx≡fy =
  let uniq = A≃B .snd .equiv-proof (A≃B .fst y) .snd
      x≡idx i = uniq (x , fx≡fy) (~ i) .fst
      idx≡y i = uniq (y , refl) i .fst
  in x≡idx ; idx≡y

refl-↣ : A ↣ A
refl-↣ .fst = id
refl-↣ .snd _ _ = id
\end{code}
