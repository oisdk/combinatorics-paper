{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Operations {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Operations.Functor     rng public
open import Algebra.Construct.Free.Semimodule.Operations.Applicative rng public
open import Algebra.Construct.Free.Semimodule.Operations.Monad       rng public
open import Algebra.Construct.Free.Semimodule.Operations.Union       rng public
open import Algebra.Construct.Free.Semimodule.Operations.Condition   rng public
open import Algebra.Construct.Free.Semimodule.Operations.Expect      rng sIsSet public
