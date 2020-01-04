\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.Search where

open import Cardinality.Finite
open import Prelude hiding (I)
open import Data.List.Relation.Unary
open import Data.List as List using (List; _∷_; []; _!_)
open import Relation.Nullary


data ReflectFound (A : Type a) {p} (P : A → Type p) : Bool → Type (a ℓ⊔ p) where
  all′ : (∀ x → P x) → ReflectFound A P true
  except′ : ∃[ x ] ¬ P x → ReflectFound A P false

Found : ∀ (A : Type a) {p} (P : A → Type p) → Type (a ℓ⊔ p)
Found A P = Σ Bool (ReflectFound A P)

pattern all p = true , all′ p
pattern except p = false , except′ p

module _ {a} {A : Type a} {p} {P : A → Type p} where
\end{code}
%<*all-comb>
\begin{code}
  ◻⟨sup⟩⇒◻ : (xs : ℰ A) → ◻ P (xs .fst) → ∀ x → P x
  ◻⟨sup⟩⇒◻ xs ∀Pxs = uncurry (λ n p → subst P p (∀Pxs n)) ∘ xs .snd

  ◻⇒◻⟨sup⟩ : (xs : List A) → (∀ x → P x) → ◻ P xs
  ◻⇒◻⟨sup⟩ xs ∀Pxs n = ∀Pxs (xs ! n)
\end{code}
%</all-comb>
%<*counterexample-def>
\begin{code}
  data Counterexample (x : A) : Type₀ where
\end{code}
%</counterexample-def>
\begin{code}
  Pass : Found A P → Type₀
  Pass (all    _) = ⊤
  Pass (except x) = Counterexample (x .fst)

  search : (ka : ℰ A) → (P? : ∀ x → Dec (P x)) → Found A P
  search ka P? = go ka P? (Search.search P? (ka .fst))
    where
    go : (ka : ℰ A) → (P? : ∀ x → Dec (P x)) → Search.Found P (ka .fst) → Found A P
    go ka P? fnd .fst = fnd .Search.found?
    go ka P? fnd .snd with fnd .Search.result
    go ka P? record { found? = .true ; result = result } .snd | Search.all′ x = all′ (◻⟨sup⟩⇒◻ ka x)
    go ka P? record { found? = .false ; result = result } .snd | Search.except′ (n , ¬Px) = except′ ((ka .fst ! n) , ¬Px)

  found-witness : {s : Found A P} → Pass s → ∀ x → P x
  found-witness {all x} p = x

  module NonInst where
\end{code}
%<*lift-forall>
\begin{code}
    ∀? : ℰ A → (∀ x → Dec (P x)) → Dec (∀ x → P x)
    ∀? fa P? =  ⟦yes ◻⟨sup⟩⇒◻ fa
                ,no ◻⇒◻⟨sup⟩ (fa .fst)
                ⟧ (Forall.◻? P P? (fa .fst))
\end{code}
%</lift-forall>
%<*auto>
\begin{code}
    ∀↯ : (fa : ℰ A) → (P? : ∀ x → Dec (P x)) → ⦃ _ : True (∀? fa P?) ⦄ → ∀ x → P x
    ∀↯ _ _ ⦃ t ⦄ = toWitness t
\end{code}
%</auto>
%<*auto-inst>
\begin{code}
  ∀↯  :  ⦃ fn : ℰ A ⦄
      →  (P? : ∀ x → Dec (P x))
      →  ⦃ _ : Pass (search fn P?) ⦄
      →  ∀ x → P x
  ∀↯ ⦃ ka ⦄ P? ⦃ p ⦄ = found-witness p
\end{code}
%</auto-inst>
\begin{code}
  ∀? : ⦃ _ : ℰ A ⦄ → (P? : ∀ x → Dec (P x)) → Dec (∀ x → P x)
  ∀? ⦃ ka ⦄ P? = ⟦yes ◻⟨sup⟩⇒◻ ka ,no ◻⇒◻⟨sup⟩ (ka .fst) ⟧ (Forall.◻? P P? (ka .fst))

  ∃? : ⦃ ka : ℰ A ⦄ → (P? : ∀ x → Dec (P x)) → Dec (∃[ x ] P x)
  ∃? ⦃ ka ⦄ P? =
      ⟦yes map-Σ (ka .fst !_) id
      ,no (λ { (x , px) → map₂ (flip (subst P) px ∘ sym) (ka .snd x) })
      ⟧ (Exists.◇? P P? (ka .fst))

  ∃↯ : ⦃ ka : ℰ A ⦄ → (P? : ∀ x → Dec (P x)) → ⦃ _ : True (∃? P?)  ⦄ → Σ A P
  ∃↯ ⦃ ka ⦄ P? ⦃ p ⦄ = toWitness p

open import Data.Product.N-ary
open import Data.Vec.Iterated as Vec
open import Cardinality.Finite.Instances

tup-inst′ : ∀ n {ls} {Xs : Types (suc n) ls} → ⦅ map-types ℰ Xs ⦆⁺ → ℰ ⦅ Xs ⦆⁺
tup-inst′ zero x = x
tup-inst′ (suc n) (x , xs) = x |×| tup-inst′ n xs

tup-inst : ∀ n {ls} {Xs : Types n ls} → ⦅ map-types ℰ Xs ⦆ → ℰ ⦅ Xs ⦆
tup-inst zero xs = fin-top′
tup-inst (suc n) xs = tup-inst′ n xs

Dec⇔ : (B ⇔ A) → Dec A → Dec B
Dec⇔ A⇔B = ⟦yes A⇔B .inv ,no A⇔B .fun ⟧

module _ (n : ℕ)
         {ls ℓ}
         {Xs : Types n ls}
         {P : ⦅ Xs ⦆ → Type ℓ}
         where
\end{code}
%<*all-nary>
\begin{code}
  ∀?ⁿ  :   ⦅ map-types ℰ Xs ⦆[ inst ]→
           xs ⦂⦅ Xs ⦆Π[ expl ]→
           Dec (P xs) [ expl ]→
           Dec (xs ⦂⦅ Xs ⦆Π[ expl ]→ P xs)
  ∀?ⁿ  =  [ n ^ inst $] .inv λ fs
       →  Dec⇔ Π[ n ^ expl $]
       ∘  ∀? ⦃ tup-inst n fs ⦄
       ∘  Π[ n ^ expl $] .fun
\end{code}
%</all-nary>
\begin{code}
  ∃?ⁿ :  ⦅ map-types ℰ Xs ⦆[ inst ]→
      (  xs ⦂⦅ Xs ⦆Π[ expl ]→ Dec (P xs) →
         Dec (Σ ⦅ Xs ⦆ P))
  ∃?ⁿ =
    [ n ^ inst $] .inv
      λ fs P? →
          (∃? ⦃ tup-inst n fs ⦄ (Π[ n ^ expl $] .fun P?))

  ∀↯ⁿ : insts ⦂⦅ map-types ℰ Xs ⦆Π[ inst ]→
      ( (P? : xs ⦂⦅ Xs ⦆Π[ expl ]→ Dec (P xs))
      → ⦃ _ : Pass (search (tup-inst n insts) (Π[ n ^ expl $] .fun P?)) ⦄
      → xs ⦂⦅ Xs ⦆Π[ expl ]→ P xs)
  ∀↯ⁿ = Π[ n ^ inst $] .inv λ fs P? ⦃ p ⦄ → Π[ n ^ expl $] .inv (found-witness p)

  ∃↯ⁿ : insts ⦂⦅ map-types ℰ Xs ⦆Π[ inst ]→
      ( (P? : xs ⦂⦅ Xs ⦆Π[ expl ]→ Dec (P xs))
      → ⦃ _ : True (∃? ⦃ tup-inst n insts ⦄ (Π[ n ^ expl $] .fun P?) ) ⦄
      → Σ ⦅ Xs ⦆ P)
  ∃↯ⁿ = Π[ n ^ inst $] .inv (λ fs P? ⦃ p ⦄ → toWitness p)

-- open import Data.Bool
-- open import Data.Bool.Properties using () renaming (discreteBool to _≟_)

-- ∧-comm : ∀ x y → x ∧ y ≡ y ∧ x
-- ∧-comm = ∀↯ⁿ 2 λ x y → (x ∧ y) ≟ (y ∧ x)
