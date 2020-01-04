\begin{code}
{-# OPTIONS --cubical --safe #-}
module Algebra.Construct.Free.CommutativeMonoid.AST where

open import Prelude
open import Algebra
\end{code}
%<*definition>
\begin{code}
data ⟅_⟆ (A : Type a) : Type a where
  ε      : ⟅ A ⟆
  _∙_    : ⟅ A ⟆ → ⟅ A ⟆ → ⟅ A ⟆
  [_]    : A → ⟅ A ⟆
  ε∙     : ∀ x → ε ∙ x ≡ x
  ∙ε     : ∀ x → x ∙ ε ≡ x
  assoc  : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
  com    : ∀ x y → x ∙ y ≡ y ∙ x
\end{code}
%</definition>
