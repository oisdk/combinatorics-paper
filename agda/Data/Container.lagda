\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Container where

open import Prelude

infix 5 _▷_
\end{code}
%<*def>
\begin{code}
record Container (s p : Level) : Type (ℓ-suc (s ℓ⊔ p)) where
  constructor _▷_
  field
    Shape     : Type s
    Position  : Shape → Type p
\end{code}
%</def>
\begin{code}
open Container public

\end{code}
%<*interp>
\begin{code}
⟦_⟧ : ∀ {s p ℓ} → Container s p → Type ℓ → Type (s ℓ⊔ p ℓ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] (P s → X)
\end{code}
%</interp>
\begin{code}
map : ∀ {s p} {C : Container s p} → (A → B) → ⟦ C ⟧ A → ⟦ C ⟧ B
map f xs .fst = xs .fst
map f xs .snd = f ∘ xs .snd
\end{code}
