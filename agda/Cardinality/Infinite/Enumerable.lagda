\begin{code}
{-# OPTIONS --cubical --safe --sized-types --postfix-projections #-}

module Cardinality.Infinite.Enumerable where

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
open import Data.Bool using (bool)

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
\end{code}
%<*convolve>
\begin{code}
convolveʳ :  (x : A) → Stream (U x) i →
             (Σ A U ⋆) × Thunk (Stream (Σ A U ⁺)) i →
             Stream (Σ A U ⁺) i
convolveʳ x ys (z  , _   ) .head = (x , ys .head) & z
convolveʳ x ys (_  , zs  ) .tail =
  let z = zs .force
  in convolveʳ x (ys .tail) (∹ z .head , delay (z .tail))

convolve : Stream A i → (∀ x → Stream (U x) i) → Stream (Σ A U ⁺) i
convolve xs ys = foldr (Stream _) (λ x zs → convolveʳ x (ys x) ([] , zs)) xs

cantor : Stream A i → (∀ x → Stream (U x) i) → Stream (Σ A U) i
cantor xs ys = concat (convolve xs ys)
\end{code}
%</convolve>
\begin{code}
module _ {a} {A : Type a} {x : A} where module ◇² = Exists (Kleene._∈⁺_ x)
import Data.List.Kleene.Relation.Unary as Kleene

infixr 5 _∈²_
_∈²_ : {A : Type a} (x : A) (xs : Stream (A ⁺) ∞) → Type a
x ∈² xs = ◇ (Kleene._∈⁺_ x) xs

convolveʳ-cover : ∀ {xᵢ : A} {yᵢ : U xᵢ} (ys : Stream (U xᵢ) ∞) (y∈ys : yᵢ ∈ ys)
                → {z : Σ A U ⋆} {zs : Thunk (Stream (Σ A U ⁺)) ∞}
                → (xᵢ , yᵢ) ∈² convolveʳ xᵢ ys (z , zs)
convolveʳ-cover ys (zero  , y∈ys) = zero , subst (λ yᵢ → (_ , yᵢ) Kleene.∈⁺ _) y∈ys (f0 , refl)
convolveʳ-cover ys (suc i , y∈ys) = ◇².push (convolveʳ-cover (ys .tail) (i , y∈ys))

shift-cover : ∀ {z z′ zs} {x : A} {ys : Stream (U x) ∞}
            → z ∈² force zs
            → z ∈² convolveʳ x ys (z′ , zs)
shift-cover (zero , z∈zs) = suc zero , Kleene.Exists.push (_≡ _) z∈zs
shift-cover (suc n , z∈zs) = ◇².push (shift-cover (n , z∈zs))

subst-head : ∀ x (xs : Stream A ∞) → xs .head ≡ x → xs ≡ x ◂ xs .tail
subst-head x xs h≡ i .head = h≡ i
subst-head x xs h≡ i .tail = xs .tail

convolve-cover : {xᵢ : A} (xs : Stream A ∞) {yᵢ : U xᵢ} (ys : ∀ x → Stream (U x) ∞)
            → xᵢ ∈ xs → yᵢ ∈ ys xᵢ → (xᵢ , yᵢ) ∈² convolve xs ys
convolve-cover xs ys (zero  , x∈xs) y∈ys = subst (λ ks → (_ , _) ∈² convolve ks ys) (sym (subst-head _ xs x∈xs)) (convolveʳ-cover  (ys _) y∈ys)
convolve-cover xs ys (suc i , x∈xs) y∈ys = shift-cover (convolve-cover (tail xs) ys (i , x∈xs) y∈ys)

cantor-cover : {x : A} {xs : Stream A ∞} {y : U x} {ys : ∀ x → Stream (U x) ∞}
            → x ∈ xs → y ∈ ys x → (x , y) ∈ cantor xs ys
cantor-cover {x = x} {xs = xs} {y = y} {ys = ys} x∈xs y∈ys = ◇-concat (_≡ _) _ (convolve-cover xs ys x∈xs y∈ys )

_|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
(xs |Σ| ys) .fst = cantor (fst xs) (fst ∘ ys)
(xs |Σ| ys) .snd (x , y) = cantor-cover (snd xs x) (snd (ys x) y)

_|×|_ : ℰ! A → ℰ! B → ℰ! (A × B)
xs |×| ys = xs |Σ| const ys

_⊎′_ : Type a → Type a → Type a
A ⊎′ B = ∃ (bool A B)

ℰ!⟨Bool⟩ : ℰ! Bool
ℰ!⟨Bool⟩ .fst .head = false
ℰ!⟨Bool⟩ .fst .tail = repeat true
ℰ!⟨Bool⟩ .snd false = zero , refl
ℰ!⟨Bool⟩ .snd true = suc zero , refl

-- _|⊎|_ : {A B : Type a} → ℰ! A → ℰ! B → ℰ! (A ⊎′ B)
-- xs |⊎| ys = ℰ!⟨Bool⟩ |Σ| bool xs ys

-- mutual
--   star-support : Stream A i → Stream (A ⋆) i
--   star-support xs .head = []
--   star-support xs .tail = map ∹_ (plus-support xs)

--   plus-support : Stream A i → Stream (A ⁺) i
--   plus-support xs = map (uncurry _&_) (cantor xs (const (star-support xs)))

-- mutual
--   star-cover : (sup : Stream A ∞) → (∀ (x : A) → x ∈ sup) → ∀ xs → xs ∈ star-support sup
--   star-cover sup fn [] = zero , refl
--   star-cover sup fn (∹ xs) = push (cong-∈ ∹_ _ (plus-cover sup fn xs))

--   plus-cover : (sup : Stream A ∞) → (∀ (x : A) → x ∈ sup) → ∀ xs → xs ∈ plus-support sup
--   plus-cover sup fn (x & xs) = cong-∈ (uncurry _&_) _ (cantor-cover {xs = sup} {ys = const (star-support sup)} (fn x) (star-cover sup fn xs))

-- star : ℰ! A → ℰ! (A ⋆)
-- plus : ℰ! A → ℰ! (A ⁺)

-- star xs .fst = star-support (xs .fst)
-- star xs .snd = star-cover (xs .fst) (xs .snd)

-- plus xs .fst = plus-support (xs .fst)
-- plus xs .snd = plus-cover (xs .fst) (xs .snd)

-- ℰ : Type a → Type a
-- ℰ A = Σ[ support ∈ Stream A ∞ ] ∀ x → ∥ x ∈ support ∥

-- open import HITs.PropositionalTruncation.Sugar

-- _∥Σ∥_ : ℰ A → (∀ x → ℰ (U x)) → ℰ (Σ A U)
-- (xs ∥Σ∥ ys) .fst = cantor (fst xs) (fst ∘ ys)
-- (xs ∥Σ∥ ys) .snd (x , y) = ⦇ cantor-cover (xs .snd x) (ys x .snd y) ⦈
-- \end{code}
