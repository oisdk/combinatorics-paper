{-# OPTIONS --cubical --safe #-}

module Data.Maybe.Properties where

open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary
open import Prelude

is-just : Maybe A → Type₀
is-just (just _) = ⊤
is-just nothing = ⊥

fromMaybe : A → Maybe A → A
fromMaybe x nothing = x
fromMaybe _ (just x) = x

from-just : (x : Maybe A) → is-just x → A
from-just (just x) _ = x

just-inj : (x y : A)  → just x ≡ just y → x ≡ y
just-inj x _ = cong (fromMaybe x)

just≢nothing : {x : A} → just x ≢ nothing
just≢nothing p = subst (maybe (const ⊤) ⊥) p tt

nothing≢just : {x : A} → nothing ≢ just x
nothing≢just p = subst (maybe (const ⊥) ⊤) p tt


discreteMaybe : Discrete A → Discrete (Maybe A)
discreteMaybe _≟_ nothing nothing = yes refl
discreteMaybe _≟_ nothing (just x) = no nothing≢just
discreteMaybe _≟_ (just x) nothing = no just≢nothing
discreteMaybe _≟_ (just x) (just y) = ⟦yes cong just ,no just-inj _ _ ⟧ (x ≟ y)
