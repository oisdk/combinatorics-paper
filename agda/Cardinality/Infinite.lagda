\begin{code}
{-# OPTIONS --cubical --safe --sized-types --postfix-projections #-}

module Cardinality.Infinite where

open import Prelude
open import Codata.Stream
open import Data.List.Kleene
open import Codata.Size
open import Codata.Thunk
open import Codata.Stream.Membership
open import Codata.Stream.Relation.Unary
import Data.List.Kleene.Membership as Kleene
open import Data.Fin
open import Function.Surjective
private
  variable
    u : Level
    U : A → Type u
\end{code}
%<*countable-def>
\begin{code}
ℰ! : Type a → Type a
ℰ! A = Σ[ support ∈ Stream A ∞ ] (∀ x → x ∈ support)
\end{code}
%</countable-def>
%<*surj>
\begin{code}
ℰ!⇒ℕ↠! : ℰ! A → (ℕ ↠! A)
ℰ!⇒ℕ↠! ca .fst i = ca .fst ! i
ℰ!⇒ℕ↠! ca .snd = ca .snd
\end{code}
%</surj>
\begin{code}
countable⟨ℕ⟩ : ℰ! ℕ
fst countable⟨ℕ⟩ = tabulate id
snd countable⟨ℕ⟩ = n∈tabulate id

interleave : (A → C) → (B → C) → Stream A i → Stream B i → Stream C i
interleave f g xs ys .head = f (xs .head)
interleave f g xs ys .tail = interleave g f ys (xs .tail)

mutual
  interleave-sndʳ : (xs : Stream A ∞) {y : B} {ys : Stream B ∞}
                    → {f : A → C} (g : B → C)
                    → (y ∈ ys) → g y ∈ interleave f g xs ys
  interleave-sndʳ xs g y∈ys = push (interleave-sndˡ (xs .tail) g y∈ys)

  interleave-sndˡ : {x : A} {xs : Stream A ∞} (ys : Stream B ∞)
                        (f : A → C) → {g : B → C}
                        → (x ∈ xs) → f x ∈ interleave f g xs ys
  interleave-sndˡ ys g (zero  , x∈xs) = zero , cong g x∈xs
  interleave-sndˡ ys g (suc n , x∈xs) = push (interleave-sndʳ ys g (n , x∈xs))

_|⊎|_ : ℰ! A → ℰ! B → ℰ! (A ⊎ B)
fst (xs |⊎| ys) = interleave inl inr (fst xs) (fst ys)
snd (xs |⊎| ys) (inl x) = interleave-sndˡ (fst ys) inl (snd xs x)
snd (xs |⊎| ys) (inr y) = interleave-sndʳ (fst xs) inr (snd ys y)
\end{code}
%<*convolve>
\begin{code}
uncons-⁺ : Stream (A ⁺) i → (A ⋆) × Thunk (Stream (A ⁺)) i
uncons-⁺ xs .fst = ∹ xs .head
uncons-⁺ xs .snd .force = xs .tail

convolveʳ : (x : A) → Stream (U x) i
          → (Σ A U ⋆) × Thunk (Stream (Σ A U ⁺)) i
          → Stream (Σ A U ⁺) i
convolveʳ x ys zs .head .head .fst = x
convolveʳ x ys zs .head .head .snd = head ys
convolveʳ x ys zs .head .tail  = zs .fst
convolveʳ x ys zs .tail = convolveʳ x (ys .tail) (uncons-⁺ (zs .snd .force))

convolveˡ : (x : A) → Stream (U x) i → Thunk (Stream (Σ A U ⁺)) i → Stream (Σ A U ⁺) i
convolveˡ x ys zs = convolveʳ x ys ([] , zs)

convolve : Stream A i → (∀ x → Stream (U x) i) → Stream (Σ A U ⁺) i
convolve xs ys = foldr (Stream ((Σ _ _) ⁺)) (λ x zs → convolveˡ x (ys x) zs) xs
\end{code}
%</convolve>
\begin{code}
cantor : Stream A i → (∀ x → Stream (U x) i) → Stream (Σ A U) i
cantor xs ys = concat (convolve xs ys)

module _ {a} {A : Type a} {x : A} where module ◇² = Exists (Kleene._∈⁺_ x)
import Data.List.Kleene.Relation.Unary as Kleene

infixr 5 _∈²_
_∈²_ : {A : Type a} (x : A) (xs : Stream (A ⁺) ∞) → Type a
x ∈² xs = ◇ (Kleene._∈⁺_ x) xs

convolveʳ-snd : ∀ {xᵢ : A} {yᵢ : U xᵢ} (ys : Stream (U xᵢ) ∞) (y∈ys : yᵢ ∈ ys)
                → {z : Σ A U ⋆} {zs : Thunk (Stream (Σ A U ⁺)) ∞}
                → (xᵢ , yᵢ) ∈² convolveʳ xᵢ ys (z , zs)
convolveʳ-snd ys (zero  , y∈ys) = zero , subst (λ yᵢ → (_ , yᵢ) Kleene.∈⁺ _) y∈ys (f0 , refl)
convolveʳ-snd ys (suc i , y∈ys) = ◇².push (convolveʳ-snd (ys .tail) (i , y∈ys))

shift-snd : ∀ {z z′ zs} {x : A} {ys : Stream (U x) ∞}
            → z ∈² force zs
            → z ∈² convolveʳ x ys (z′ , zs)
shift-snd (zero , z∈zs) = suc zero ,  Kleene.Exists.push (_≡ _) z∈zs
shift-snd (suc n , z∈zs) = ◇².push (shift-snd (n , z∈zs))

subst-head : ∀ x (xs : Stream A ∞) → xs .head ≡ x → xs ≡ x ◂ xs .tail
subst-head x xs h≡ i .head = h≡ i
subst-head x xs h≡ i .tail = xs .tail

convolve-snd : {xᵢ : A} (xs : Stream A ∞) {yᵢ : U xᵢ} (ys : ∀ x → Stream (U x) ∞)
            → xᵢ ∈ xs → yᵢ ∈ ys xᵢ → (xᵢ , yᵢ) ∈² convolve xs ys
convolve-snd xs ys (zero  , x∈xs) y∈ys = subst (λ ks → (_ , _) ∈² convolve ks ys) (sym (subst-head _ xs x∈xs)) (convolveʳ-snd  (ys _) y∈ys)
convolve-snd xs ys (suc i , x∈xs) y∈ys = shift-snd (convolve-snd (tail xs) ys (i , x∈xs) y∈ys)

cantor-snd : {x : A} {xs : Stream A ∞} {y : U x} {ys : ∀ x → Stream (U x) ∞}
            → x ∈ xs → y ∈ ys x → (x , y) ∈ cantor xs ys
cantor-snd {x = x} {xs = xs} {y = y} {ys = ys} x∈xs y∈ys = ◇-concat (_≡ _) _ (convolve-snd xs ys x∈xs y∈ys )

_|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
(xs |Σ| ys) .fst = cantor (fst xs) (fst ∘ ys)
(xs |Σ| ys) .snd (x , y) = cantor-snd (snd xs x) (snd (ys x) y)

ℰ : Type a → Type a
ℰ A = Σ[ support ∈ Stream A ∞ ] ∀ x → ∥ x ∈ support ∥

open import HITs.PropositionalTruncation.Sugar

_∥Σ∥_ : ℰ A → (∀ x → ℰ (U x)) → ℰ (Σ A U)
(xs ∥Σ∥ ys) .fst = cantor (fst xs) (fst ∘ ys)
(xs ∥Σ∥ ys) .snd (x , y) = ⦇ cantor-snd (xs .snd x) (ys x .snd y) ⦈
\end{code}
