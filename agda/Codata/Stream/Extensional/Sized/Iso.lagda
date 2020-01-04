\begin{code}

{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Stream.Extensional.Sized.Iso where

open import Codata.Size
open import Prelude
open import Data.Nat.Sized
open import Codata.Stream.Extensional.Sized.Base
import Codata.Stream.Extensional.Base as UnSized

Stream⇔SzStream : UnSized.Stream A ⇔ Stream A ∞
Stream⇔SzStream = iso-arg ℕ⇔Szℕ
\end{code}
