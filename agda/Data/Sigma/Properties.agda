{-# OPTIONS --cubical --safe #-}

module Data.Sigma.Properties where

open import Prelude
open import Cubical.Foundations.HLevels using (ΣProp≡) public

reassoc : {A : Type a} {B : A → Type b} {C : Σ A B → Type c} → Σ (Σ A B) C ⇔ (Σ[ x ⦂ A ] Σ[ y ⦂ B x ] C (x , y))
reassoc .fun ((x , y) , z) = x , (y , z)
reassoc .inv (x , (y , z)) = (x , y) , z
reassoc .rightInv _ = refl
reassoc .leftInv  _ = refl
