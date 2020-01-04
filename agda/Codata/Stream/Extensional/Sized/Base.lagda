\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Stream.Extensional.Sized.Base where

open import Codata.Size
open import Prelude
open import Data.Nat.Sized

Stream : Type a → Size → Type a
Stream A i = Szℕ i → A
\end{code}
