\begin{code}
{-# OPTIONS --cubical --safe #-}

module Function.Injective.Properties where

open import Level
open import Path
open import Data.Sigma
open import Function.Injective.Base
open import Relation.Nullary.Decidable
open import Relation.Nullary.Discrete
A↣Discrete⇒Discrete⟨A⟩ :
\end{code}
%<*inj-discrete>
\begin{code}
 A ↣ B → Discrete B → Discrete A
\end{code}
%</inj-discrete>
\begin{code}
A↣Discrete⇒Discrete⟨A⟩ (f , inj) _≟_ x y = ⟦yes inj x y ,no cong f ⟧ (f x ≟ f y)
\end{code}
