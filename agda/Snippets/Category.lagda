\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Category where

open import Level

Ob : Type₁
Hom : Type₁

\end{code}
%<*ob-wrong>
\begin{code}
Ob = Type₀
\end{code}
%</ob-wrong>
%<*hom-wrong>
\begin{code}
Hom = Ob → Ob
\end{code}
%</hom-wrong>
