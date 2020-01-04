{-# OPTIONS --cubical --safe #-}

module Lens where

open import Prelude

record LensPart (A : Set a) (B : Set b) : Set (a ℓ⊔ b) where
  field
    get : B
    set : B → A
open LensPart public

record Lens (A : Set a) (B : Set b) : Set (a ℓ⊔ b) where
  field
    into : A → LensPart A B
    get-set : ∀ s v → into (into s .set v) .get ≡ v
    set-get : ∀ s → into s .set (into s .get) ≡ s
    set-set : ∀ s v₁ v₂ → into (into s .set v₁) .set v₂ ≡ into s .set v₂
open Lens public

infixl 4.5 _[_] _[_]≔_
_[_] : A → Lens A B → B
xs [ l ] = l .into xs .get

_[_]≔_ : A → Lens A B → B → A
xs [ l ]≔ x = l .into xs .set x

infixr 9 _⋯_
_⋯_ : Lens A B → Lens B C → Lens A C
(ab ⋯ bc) .into xs =
  let ab-xs = ab .into xs
      bc-ys = bc .into (ab-xs .get)
  in λ where .get → bc-ys .get
             .set → ab-xs .set ∘ bc-ys .set
(ab ⋯ bc) .get-set s v = cong _[ bc ] (ab .get-set s _) ; bc .get-set (ab .into s .get) v
(ab ⋯ bc) .set-get s = cong (s [ ab ]≔_) (bc .set-get (ab .into s .get)) ; ab .set-get s
(ab ⋯ bc) .set-set s v₁ v₂ = ab .set-set s _ _ ; cong (s [ ab ]≔_) (cong (_[ bc ]≔ v₂) (ab .get-set _ _) ; bc .set-set _ _ _)

⦅fst⦆ : Lens (A × B) A
⦅fst⦆ .into (x , y) =
  λ where .get → x
          .set z → z , y
⦅fst⦆ .get-set _ _ = refl
⦅fst⦆ .set-get _ = refl
⦅fst⦆ .set-set _ _ _ = refl

⦅snd⦆ : Lens (A × B) B
⦅snd⦆ .into (x , y) =
  λ where .get → y
          .set z → x , z
⦅snd⦆ .get-set _ _ = refl
⦅snd⦆ .set-get _ = refl
⦅snd⦆ .set-set _ _ _ = refl

private variable n m : ℕ
open import Data.Nat.Order
open import Data.Vec.Iterated

⦅ix⦆ : ∀ n → n < m → Lens (Vec A m) A
⦅ix⦆ {suc m} zero p = ⦅fst⦆
⦅ix⦆ {suc m} (suc n) p = ⦅snd⦆ ⋯ ⦅ix⦆ n p
