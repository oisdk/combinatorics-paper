{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open import Algebra.Construct.Free.Semimodule.Definition  rng public
open import Algebra.Construct.Free.Semimodule.Eliminators rng public
open import Algebra.Construct.Free.Semimodule.Operations  rng sIsSet public
