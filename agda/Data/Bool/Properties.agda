{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Bool.Properties where

open import Prelude
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary

discreteBool : Discrete Bool
discreteBool false y .does = not y
discreteBool true  y .does = y
discreteBool false false .why = ofʸ refl
discreteBool false true .why = ofⁿ λ p → subst (bool′ Bool ⊥) p true
discreteBool true false .why = ofⁿ λ p → subst (bool′ ⊥ Bool) p true
discreteBool true true .why = ofʸ refl

isPropT : ∀ x → isProp (T x)
isPropT false ()
isPropT true x _ _ = x

T? : ∀ x → Dec (T x)
T? x .does = x
T? false .why = ofⁿ id
T? true  .why = ofʸ tt

_&_≲ᵇ_ : Bool → Bool → Bool → Bool
s & false ≲ᵇ false = s
s & true  ≲ᵇ true  = s
_ & true  ≲ᵇ false = false
_ & false ≲ᵇ true  = true

_&_≲_ : Bool → Bool → Bool → Type₀
s & x ≲ y = T (s & x ≲ᵇ y)

_<ᵇ_ _≤ᵇ_ : Bool → Bool → Bool
_<ᵇ_ = false &_≲ᵇ_
_≤ᵇ_ = true  &_≲ᵇ_


_<_ _≤_ : Bool → Bool → Type₀
x < y = T (x <ᵇ y)
x ≤ y = T (x ≤ᵇ y)

_<?_ : ∀ x y → Dec (x < y)
x <? y = T? (x <ᵇ y)

_≤?_ : ∀ x y → Dec (x ≤ y)
x ≤? y = T? (x ≤ᵇ y)

≲-trans : ∀ s x y z i j → i & x ≲ y → j & y ≲ z → (s ∨ (i ∧ j)) & x ≲ z
≲-trans s     false y     true  i    j x≲y y≲z = tt
≲-trans true  false false false i    j x≲y y≲z = tt
≲-trans true  true  true  true  i    j x≲y y≲z = tt
≲-trans false false false false true j x≲y y≲z = y≲z
≲-trans false true  true  true  true j x≲y y≲z = y≲z

≤-refl : ∀ x → x ≤ x
≤-refl false = tt
≤-refl true  = tt

≤-antisym : ∀ x y → x ≤ y → y ≤ x → x ≡ y
≤-antisym false false x≤y y≤x = refl
≤-antisym true  true  x≤y y≤x = refl

≤-totalOrder : TotalOrder Bool ℓ-zero
≤-totalOrder .TotalOrder.partialOrder .PartialOrder._≤_ = _≤_
≤-totalOrder .TotalOrder.partialOrder .PartialOrder.refl = ≤-refl _
≤-totalOrder .TotalOrder.partialOrder .PartialOrder.antisym = ≤-antisym _ _
≤-totalOrder .TotalOrder.partialOrder .PartialOrder.trans = ≲-trans true _ _ _ true true
≤-totalOrder .TotalOrder._≤?_ false false = inl tt
≤-totalOrder .TotalOrder._≤?_ false true  = inl tt
≤-totalOrder .TotalOrder._≤?_ true  false = inr tt
≤-totalOrder .TotalOrder._≤?_ true  true  = inl tt
