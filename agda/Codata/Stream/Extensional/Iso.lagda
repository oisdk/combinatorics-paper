\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Stream.Extensional.Iso where

open import Prelude

open import Codata.Stream renaming (Stream to IntStream)
open import Codata.Stream.Extensional.Base using (Stream)
open import Codata.Stream.Extensional.Sized renaming (Stream to SzStream)
open import Codata.Size
open import Data.Nat.Sized

tab : SzStream A i → IntStream A i
tab xs .head = xs zero
tab xs .tail = tab (xs ∘ suc)

detab : IntStream A i → SzStream A i
detab xs zero = xs .head
detab xs (suc n) = detab (xs .tail) n

E→S→E : (xs : SzStream A i) → detab {i = i} (tab {i = i} xs) ≡ xs
E→S→E xs i zero = xs zero
E→S→E xs i (suc n) = E→S→E (xs ∘ suc) i n

S→E→S : (xs : IntStream A i) → tab {i = i} (detab {i = i} xs) ≡ xs
S→E→S xs i .head = xs .head
S→E→S xs i .tail = S→E→S (xs .tail) i

SzStream⇔IntStream : SzStream A i ⇔ IntStream A i
SzStream⇔IntStream .fun = tab
SzStream⇔IntStream .inv = detab
SzStream⇔IntStream .leftInv = E→S→E
SzStream⇔IntStream .rightInv = S→E→S

Ext⇔Int : Stream A ⇔ IntStream A ∞
Ext⇔Int = Stream⇔SzStream ⟨ trans-⇔ ⟩ SzStream⇔IntStream
\end{code}
