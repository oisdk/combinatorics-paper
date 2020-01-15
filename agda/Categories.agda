{-# OPTIONS --cubical --safe --postfix-projections #-}

module Categories where

open import Prelude

record PreCategory ℓ₁ ℓ₂ : Type (ℓsuc (ℓ₁ ℓ⊔ ℓ₂)) where
  field
    Ob   : Type ℓ₁
    Hom  : Ob → Ob → Type ℓ₂
    Id   : ∀ {X} → Hom X X
    Comp : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    assoc-Comp : ∀ {W X Y Z}
                   (f : Hom Y Z)
                   (g : Hom X Y)
                   (h : Hom W X) →
                   Comp f (Comp g h) ≡ Comp (Comp f g) h
    Comp-Id : ∀ {X Y} (f : Hom X Y) → Comp f Id ≡ f
    Id-Comp : ∀ {X Y} (f : Hom X Y) → Comp Id f ≡ f
    Hom-Set : ∀ {X Y} → isSet (Hom X Y)

  infixr 0 _⟶_
  _⟶_ = Hom

  infixl 0 _⟵_
  _⟵_ = flip Hom

  infixr 9 _·_
  _·_ = Comp

  variable
    X Y Z : Ob

  Isomorphism : (X ⟶ Y) → Type ℓ₂
  Isomorphism {X} {Y} f = Σ[ g ⦂ Y ⟶ X ] ((g · f ≡ Id) × (f · g ≡ Id))

  infix 4 _≅_
  _≅_ : Ob → Ob → Type _
  X ≅ Y = Σ (X ⟶ Y) Isomorphism

  module _ {X Y : Ob} where
    Monic : (X ⟶ Y) → Type _
    Monic f = ∀ {Z} → (g₁ g₂ : Z ⟶ X) → f · g₁ ≡ f · g₂ → g₁ ≡ g₂

    Epic : (X ⟶ Y) → Type _
    Epic f = ∀ {Z} → (g₁ g₂ : Y ⟶ Z) → g₁ · f ≡ g₂ · f → g₁ ≡ g₂

  IsInitial : Ob → Type _
  IsInitial I = ∀ {X} → isContr (I ⟶ X)

  IsTerminal : Ob → Type _
  IsTerminal T = ∀ {X} → isContr (X ⟶ T)

  Initial = ∃ IsInitial
  Terminal = ∃ IsTerminal

  refl-≅ : X ≅ X
  refl-≅ .fst = Id
  refl-≅ .snd .fst = Id
  refl-≅ .snd .snd .fst = Comp-Id Id
  refl-≅ .snd .snd .snd = Comp-Id Id

  sym-≅ : X ≅ Y → Y ≅ X
  sym-≅ X≅Y .fst = X≅Y .snd .fst
  sym-≅ X≅Y .snd .fst = X≅Y .fst
  sym-≅ X≅Y .snd .snd .fst = X≅Y .snd .snd .snd
  sym-≅ X≅Y .snd .snd .snd = X≅Y .snd .snd .fst

  open import Path.Reasoning

  trans-≅ : X ≅ Y → Y ≅ Z → X ≅ Z
  trans-≅ X≅Y Y≅Z .fst = Y≅Z .fst · X≅Y .fst
  trans-≅ X≅Y Y≅Z .snd .fst = X≅Y .snd .fst · Y≅Z .snd .fst
  trans-≅ X≅Y Y≅Z .snd .snd .fst =
    (X≅Y .snd .fst · Y≅Z .snd .fst) · (Y≅Z .fst · X≅Y .fst) ≡⟨ assoc-Comp (X≅Y .snd .fst · Y≅Z .snd .fst) (Y≅Z .fst) (X≅Y .fst) ⟩
    ((X≅Y .snd .fst · Y≅Z .snd .fst) · Y≅Z .fst) · X≅Y .fst ≡˘⟨ cong (_· X≅Y .fst) (assoc-Comp (X≅Y .snd .fst) (Y≅Z .snd .fst) (Y≅Z .fst)) ⟩
    (X≅Y .snd .fst · (Y≅Z .snd .fst · Y≅Z .fst)) · X≅Y .fst ≡⟨ cong (λ yz → (X≅Y .snd .fst · yz) · X≅Y .fst) (Y≅Z .snd .snd .fst) ⟩
    (X≅Y .snd .fst · Id) · X≅Y .fst ≡⟨ cong (_· X≅Y .fst) (Comp-Id (X≅Y .snd .fst)) ⟩
    X≅Y .snd .fst · X≅Y .fst ≡⟨ X≅Y .snd .snd .fst ⟩
    Id ∎
  trans-≅ X≅Y Y≅Z .snd .snd .snd =
    (Y≅Z .fst · X≅Y .fst) · (X≅Y .snd .fst · Y≅Z .snd .fst) ≡⟨ assoc-Comp _ _ _ ⟩
    ((Y≅Z .fst · X≅Y .fst) · X≅Y .snd .fst) · Y≅Z .snd .fst ≡˘⟨ cong (_· Y≅Z .snd .fst) (assoc-Comp _ _ _) ⟩
    (Y≅Z .fst · (X≅Y .fst · X≅Y .snd .fst)) · Y≅Z .snd .fst ≡⟨ cong (λ xy → (Y≅Z .fst · xy) · Y≅Z .snd .fst) (X≅Y .snd .snd .snd) ⟩
    (Y≅Z .fst · Id) · Y≅Z .snd .fst ≡⟨ cong (_· Y≅Z .snd .fst) (Comp-Id _) ⟩
    Y≅Z .fst · Y≅Z .snd .fst ≡⟨ Y≅Z .snd .snd .snd ⟩
    Id ∎

  idToIso : X ≡ Y → X ≅ Y
  idToIso {X} {Y} X≡Y = subst (X ≅_) X≡Y refl-≅
