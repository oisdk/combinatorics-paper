{-# OPTIONS --cubical --postfix-projections #-}

module Countdown where

open import Prelude hiding (C)
open import Data.List
open import Data.Fin

open import Literals.Number
open import Data.Nat.Literals
open import Data.Fin.Literals
open import Data.Nat using (_+_; _*_)
open import Data.Nat.Properties using (pred)
open import Data.Fin.Properties using (FinToℕ)
open import Agda.Builtin.Nat using (_-_; _==_)

data Op : Type₀ where
  plus times sub : Op

private
  variable
    n k : ℕ

Vec : Type a → ℕ → Type a
Vec A zero = Lift _ ⊤
Vec A (suc n) = A × Vec A n

Subseq : ℕ → Type₀
Subseq = Vec Bool

Perm : ℕ → Type₀
Perm zero    = ⊤
Perm (suc n) = Fin (suc n) × Perm n

count : Subseq n → ℕ
count {n = zero}  _        = 0
count {n = suc n} (x , xs) = bool 0 1 x + count xs

Comb : ℕ → Type₀
Comb n = Σ[ s ⦂ Subseq n ] Perm (count s)

{-# TERMINATING #-}
BinTree : ℕ → Type₀
BinTree zero = ⊥
BinTree (suc zero) = ⊤
BinTree (suc (suc n)) = Op × Σ[ i ⦂ Fin (suc n) ] BinTree (suc (FinToℕ i)) × BinTree (suc n - FinToℕ i)

open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Function.Surjective.Properties

ℰ!⟨Fin⟩ : ℰ! (Fin n)
ℰ!⟨Fin⟩ = 𝕃⇔ℒ⟨ℰ!⟩ .inv (ℰ!⇔Fin↠! .inv (_ , ↠!-ident))

ℰ!⟨Vec⟩ : ℰ! A → ℰ! (Vec A n)
ℰ!⟨Vec⟩ {n = zero} ℰ!⟨A⟩ = ℰ!⟨Lift⟩ ℰ!⟨⊤⟩
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

{-# TERMINATING #-}
ℰ!⟨BinTree⟩ : ℰ! (BinTree n)
ℰ!⟨BinTree⟩ {n = zero} = ℰ!⟨⊥⟩
ℰ!⟨BinTree⟩ {n = suc zero} = ℰ!⟨⊤⟩
ℰ!⟨BinTree⟩ {n = suc (suc n)} = ℰ!⟨Op⟩ |×| (ℰ!⟨Fin⟩ |Σ| λ _ → ℰ!⟨BinTree⟩ |×| ℰ!⟨BinTree⟩)

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

vecToList : Vec A n → List A
vecToList {n = zero} _ = []
vecToList {n = suc n} (x , xs) = x ∷ vecToList xs

Expr : ℕ → Type₀
Expr n = Σ[ c ⦂ Comb n ] (BinTree (count (fst c)))

ℰ!⟨Expr⟩ : ℰ! (Expr n)
ℰ!⟨Expr⟩ = ℰ!⟨Comb⟩ |Σ| λ _ → ℰ!⟨BinTree⟩

appOneOp : Op → ℕ → ℕ → ℕ
appOneOp plus = _+_
appOneOp times = _*_
appOneOp sub = _-_

splitVec : (i : Fin n) → Vec A n → Vec A (FinToℕ i) × Vec A (n - FinToℕ i)
splitVec {n = suc n} f0 xs = _ , xs
splitVec {n = suc n} (fs i) (x , xs) = map₁ (x ,_) (splitVec i xs)

{-# TERMINATING #-}
appOp : Vec ℕ n → BinTree n → ℕ
appOp {n = suc zero} (fst₁ , snd₁) ys = fst₁
appOp {n = suc (suc n)} (x , xs) (o , i , ys , zs) = let ys′ , zs′ = splitVec i xs in appOneOp o (appOp (x , ys′) ys) (appOp zs′ zs)

runExpr : (xs : List ℕ) → Expr (length xs) → ℕ
runExpr xs ((subs , perm) , ops) = appOp (runPerm perm (runSubseq xs subs)) ops

take : ℕ → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

filter : (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs


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

{-# TERMINATING #-}
appToDisp : Vec ℕ n → BinTree n → Disp
appToDisp {n = suc zero} (fst₁ , snd₁) ys = primForce fst₁ lit
appToDisp {n = suc (suc n)} (x , xs) (o , i , ys , zs) =
  let ys′ , zs′ = splitVec i xs
      ys″ = appToDisp (x , ys′) ys
      zs″ = appToDisp zs′ zs
  in primForce zs″ (primForce ys″ (appDispOp o))

toDisp : (xs : List ℕ) → Expr (length xs) → Disp
toDisp xs ((subs , perm) , ops) = appToDisp (runPerm perm (runSubseq xs subs)) ops

example : List Disp
example = map (toDisp nums) (take 1 (filter (λ e → runExpr nums e == 576) (ℰ!⟨Expr⟩ .fst)))
  where
  nums = (100 ∷ 25 ∷ 1 ∷ 5 ∷ 3 ∷ [])

-- Uncomment for a type error which contains the answer
prf : example ≡ (lit 0 ∷ [])
prf = refl
