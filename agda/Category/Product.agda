{-# OPTIONS --cubical --safe #-}

module Category.Product where

open import Prelude
open import Category

module _ {ℓ₁ ℓ₂} (C : Category ℓ₁ ℓ₂) where
  open Category.Category C

  module _ (X Y : Ob) where
    record Product : Type (ℓ₁ ℓ⊔ ℓ₂) where
      field
        obj : Ob
        fst : C [ obj , X ]
        snd : C [ obj , Y ]
        ump : (f : C [ Z , X ]) (g : C [ Z , Y ]) →
              ∃![ f×g ] ((C [ fst ∘ f×g ] ≡ f) × (C [ snd ∘ f×g ] ≡ g))

  record HasProducts : Type (ℓ₁ ℓ⊔ ℓ₂) where
    field product : (X Y : Ob) → Product X Y
