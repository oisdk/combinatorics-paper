{-# OPTIONS --cubical --postfix-projections --safe #-}

module Countdown where

open import Prelude hiding (C)
open import Data.List
open import Data.Fin

open import Literals.Number
open import Data.Nat.Literals
open import Data.Fin.Literals
open import Data.Nat using (_+_; _*_)
open import Data.Nat.Properties using (pred; _<_)
open import Data.Fin.Properties using (FinToℕ)
open import Agda.Builtin.Nat using (_-_; _==_)
open import Dyck
open import Data.Vec.Iterated

data Op : Type₀ where
  plus times sub : Op

private
  variable
    n m k : ℕ

Subseq : ℕ → Type₀
Subseq = Vec Bool

Perm : ℕ → Type₀
Perm zero    = ⊤
Perm (suc n) = Fin (suc n) × Perm n

count : Subseq n → ℕ
count = foldr′ (λ x xs → bool 0 1 x + xs) 0

Comb : ℕ → Type₀
Comb n = Σ[ s ⦂ Subseq n ] Perm (count s)

open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Function.Surjective.Properties

ℰ!⟨Fin⟩ : ℰ! (Fin n)
ℰ!⟨Fin⟩ = 𝕃⇔ℒ⟨ℰ!⟩ .inv (ℰ!⇔Fin↠! .inv (_ , ↠!-ident))

import Data.Unit.UniversePolymorphic as Poly

ℰ!⟨Poly⊤⟩ : ∀ {ℓ} → ℰ! (Poly.⊤ {ℓ})
ℰ!⟨Poly⊤⟩ .fst = _ ∷ []
ℰ!⟨Poly⊤⟩ .snd _ = f0 , refl

ℰ!⟨Vec⟩ : ℰ! A → ℰ! (Vec A n)
ℰ!⟨Vec⟩ {n = zero} ℰ!⟨A⟩ = ℰ!⟨Poly⊤⟩
ℰ!⟨Vec⟩ {n = suc n} ℰ!⟨A⟩ = ℰ!⟨A⟩ |×| ℰ!⟨Vec⟩ ℰ!⟨A⟩

ℰ!⟨Subseq⟩ : ℰ! (Subseq n)
ℰ!⟨Subseq⟩ = ℰ!⟨Vec⟩ ℰ!⟨2⟩

ℰ!⟨Perm⟩ : ℰ! (Perm n)
ℰ!⟨Perm⟩ {n = zero} = ℰ!⟨⊤⟩
ℰ!⟨Perm⟩ {n = suc n} = ℰ!⟨Fin⟩ |×| ℰ!⟨Perm⟩

ℰ!⟨Comb⟩ : ℰ! (Comb n)
ℰ!⟨Comb⟩ = ℰ!⟨Subseq⟩ |Σ| λ _ → ℰ!⟨Perm⟩

ℰ!⟨Op⟩ : ℰ! Op
ℰ!⟨Op⟩ .fst = plus ∷ times ∷ sub ∷ []
ℰ!⟨Op⟩ .snd plus = 0 , refl
ℰ!⟨Op⟩ .snd times = 1 , refl
ℰ!⟨Op⟩ .snd sub = 2 , refl

runSubseq : (xs : List A) → (ys : Subseq (length xs)) → Vec A (count ys)
runSubseq []       ys = _
runSubseq (x ∷ xs) (false , snd₁) = runSubseq xs snd₁
runSubseq (x ∷ xs) (true , snd₁) = x , runSubseq xs snd₁

insert : A → Fin (suc n) → Vec A n → Vec A (suc n)
insert x f0 xs = x , xs
insert {n = suc _} x (fs i) (x₂ , xs) = x₂ , insert x i xs

runPerm : Perm n → Vec A n → Vec A n
runPerm {n = zero} ps _ = _
runPerm {n = suc n} (fst₁ , snd₁) (x , xs) = insert x fst₁ (runPerm snd₁ xs)

runComb : (xs : List A) → (c : Comb (length xs)) → Vec A (count (c .fst))
runComb xs (subs , perm) = runPerm perm (runSubseq xs subs)

ExprTree : ℕ → Type₀
ExprTree zero    = ⊥
ExprTree (suc n) = Dyck 0 n × Vec Op n

ℰ!⟨ExprTree⟩ : ℰ! (ExprTree n)
ℰ!⟨ExprTree⟩ {n = zero} = ℰ!⟨⊥⟩
ℰ!⟨ExprTree⟩ {n = suc n} = ℰ!⟨Dyck⟩ |×| ℰ!⟨Vec⟩ ℰ!⟨Op⟩

Expr : ℕ → Type₀
Expr n = Σ[ c ⦂ Comb n ] (ExprTree (count (fst c)))

ℰ!⟨Expr⟩ : ℰ! (Expr n)
ℰ!⟨Expr⟩ = ℰ!⟨Comb⟩ |Σ| λ _ → ℰ!⟨ExprTree⟩

buildExpr : (xs : List ℕ) → Expr (length xs) → Tree Op ℕ
buildExpr xs (comb , tree) with count (comb .fst) | runComb xs comb
buildExpr xs (comb , (tree , ops)) | suc n | ys = fromDyck tree ops ys

appOneOp : Op → ℕ → ℕ → ℕ
appOneOp plus = _+_
appOneOp times = _*_
appOneOp sub = _-_

runTree : Tree Op ℕ → ℕ
runTree (leaf x) = x
runTree (node o xs ys) = appOneOp o (runTree xs) (runTree ys)

data Disp : Type₀ where
  lit : ℕ → Disp
  _⟨+⟩_ : Disp → Disp → Disp
  _⟨*⟩_ : Disp → Disp → Disp
  _⟨-⟩_ : Disp → Disp → Disp

appDispOp : Op → Disp → Disp → Disp
appDispOp plus  = _⟨+⟩_
appDispOp times = _⟨*⟩_
appDispOp sub   = _⟨-⟩_

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

dispTree : Tree Op ℕ → Disp
dispTree (leaf x) = lit x
dispTree (node o xs ys) = (appDispOp o $! dispTree xs) $! dispTree ys

take : ℕ → List A → List A
take zero _ = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

filter : (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

example : List Disp
example = map dispTree (take 1 (filter (λ e → runTree e == 576) (map (buildExpr nums) (ℰ!⟨Expr⟩ .fst))))
  where
  nums = (100 ∷ 25 ∷ 1 ∷ 5 ∷ 3 ∷ [])

-- Uncomment for a type error which contains the answer
-- prf : example ≡ (lit 0 ∷ [])
-- prf = refl
