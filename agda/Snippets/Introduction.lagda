\begin{code}
module Snippets.Introduction where

open import Level
\end{code}
%<*bot>
\begin{code}
data ⊥ : Type₀ where
\end{code}
%</bot>
%<*top>
\begin{code}
record ⊤ : Type₀ where
  constructor tt
\end{code}
%</top>
%<*bool>
\begin{code}
data Bool : Type₀ where
  true   : Bool
  false  : Bool
\end{code}
%</bool>
%<*sigma>
\begin{code}
record Σ (A : Type a) (B : A → Type b) : Type (a ℓ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
\end{code}
%</sigma>
\begin{code}
∃ : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃ {A = A} = Σ A

infixr 4.5 ∃-syntax
∃-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → e) = ∃[ x ] e

infixr 4.5 Σ⦂-syntax
Σ⦂-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ⦂-syntax = Σ

syntax Σ⦂-syntax t (λ x → e) = Σ[ x ⦂ t ] e

module _ {a b} {A : Type a} {B : A → Type b} where
  example₁ : Type _
  example₁ =
\end{code}
%<*sigma-syntax-1>
\begin{code}[inline]
    Σ A B
\end{code}
%</sigma-syntax-1>
\begin{code}
  example₂ : Type _
  example₂ =
\end{code}
%<*sigma-syntax-2>
\begin{code}[inline]%
    ∃ B
\end{code}
%</sigma-syntax-2>
\begin{code}
  example₃ : Type _
\end{code}
\begin{code}
  example₃ =
\end{code}
%<*sigma-syntax-3>
\begin{code}[inline]
    Σ[ x ⦂ A ] B x
\end{code}
%</sigma-syntax-3>
