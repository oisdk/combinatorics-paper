{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Sugar where

open import Data.Maybe
open import Prelude

pure : A → Maybe A
pure = just

_<*>_ : Maybe (A → B) → Maybe A → Maybe B
nothing <*> _ = nothing
just f  <*> nothing = nothing
just f <*> just x   = just (f x)

_>>=_ : Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just x  >>= f = f x
