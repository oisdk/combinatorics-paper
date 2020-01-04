\begin{code}
{-# OPTIONS --cubical --sized-types #-}
module Snippets.Introduction where

open import Cubical.Foundations.Everything using (~_)
open import Path using (_≡_) renaming (cong to cong′)
open import Level
open import Data.Product
open import Data.Nat using (ℕ; suc; zero)
\end{code}
%<*top>
\begin{code}
record ⊤ : Type₀ where constructor tt
\end{code}
%</top>
%<*refl-sym>
\begin{code}
refl : {x : A} → x ≡ x
refl {x = x} = λ i → x

sym : {x y : A} → x ≡ y → y ≡ x
sym x≡y i = x≡y (~ i)
\end{code}
%</refl-sym>
%<*funExt>
\begin{code}
funExt : {A : Type a} {B : A → Type a} {f g : (x : A) → B x} →
         ((x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i
\end{code}
%</funExt>
%<*cong>
\begin{code}
cong : ∀ {x y} (f : A → B) → x ≡ y → f x ≡ f y
\end{code}
%</cong>
\begin{code}
cong = cong′
\end{code}
%<*isProp>
\begin{code}
isProp : Type a → Type a
isProp A = (x y : A) → x ≡ y
\end{code}
%</isProp>
%<*isSet>
\begin{code}
isSet : Type a → Type a
isSet A = (x y : A) → isProp (x ≡ y)
\end{code}
%</isSet>
%<*isContr>
\begin{code}
isContr : Type a → Type a
isContr A = Σ[ x ∈ A ] ∀ y → x ≡ y
\end{code}
%</isContr>
\begin{code}
homotopyLevel : ℕ → Type a → Type a
homotopyLevel zero    A = isProp A
homotopyLevel (suc n) A = (x y : A) → homotopyLevel n (x ≡ y)
\end{code}
%<*add>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero   + m = m
suc n  + m = suc (n + m)
\end{code}
%</add>
%<*inc>
\begin{code}
inc : ℕ → ℕ
inc n = n + 1
\end{code}
%</inc>
%<*bool>
\begin{code}
data Bool : Type₀ where
  false  : Bool
  true   : Bool
\end{code}
%</bool>
%<*maybe>
\begin{code}
data Maybe (A : Type a) : Type a where
  nothing : Maybe A
  just : A → Maybe A
\end{code}
%</maybe>
%<*id>
\begin{code}
id : A → A
id = λ x → x
\end{code}
%</id>
%<*ifte>
\begin{code}
if_then_else_ : Bool → A → A → A
if true   then t  else _  = t
if false  then _  else f  = f
\end{code}
%</ifte>
%<*dependent>
\begin{code}
ℕorBool : (b : Bool) → if b then ℕ else Bool
ℕorBool false  = true
ℕorBool true   = 1
\end{code}
%</dependent>
%<*proof>
\begin{code}
x+0≡0 : ∀ x → x + 0 ≡ x
x+0≡0 zero     = refl
x+0≡0 (suc x)  = cong suc (x+0≡0 x)
\end{code}
%</proof>
\begin{code}
{-# TERMINATING #-}
\end{code}
%<*nonterm>
\begin{code}
nonsense : 1 ≡ 2
nonsense = nonsense
\end{code}
%</nonterm>
\begin{code}
_-_ : ℕ → ℕ → ℕ
n - zero = n
zero - suc m = zero
suc n - suc m = n - m
{-# TERMINATING #-}
\end{code}
%<*nonterm-add>
\begin{code}
_+′_ : ℕ → ℕ → ℕ
zero  +′ m = m
n     +′ m = (n - 1) +′ m
\end{code}
%</nonterm-add>
%<*stream>
\begin{code}
record Stream (A : Type a) : Type a where
  coinductive
  field
    head  : A
    tail  : Stream A
open Stream
\end{code}
%</stream>
%<*stream-prog>
\begin{code}
ℕ-from : ℕ → Stream ℕ
head  (ℕ-from n) = n
tail  (ℕ-from n) = ℕ-from (suc n)

ℕ-from-head : ∀ n → head (ℕ-from n) ≡ n
ℕ-from-head _ = refl
\end{code}
%</stream-prog>
\begin{code}
{-# TERMINATING #-}
\end{code}
%<*stream-nonterm>
\begin{code}
bad-stream : Stream A
bad-stream = bad-stream

diverge : A
diverge = head bad-stream
\end{code}
%</stream-nonterm>
\begin{code}
module BadQuot where
\end{code}
%<*badquot>
\begin{code}
 data _/_ (A : Type a) (_~_ : A → A → Type b) : Type (a ℓ⊔ b) where
   [_]    : A → A / _~_
   quot   : ∀ {x y} → x ~ y → [ x ] ≡ [ y ]
\end{code}
%</badquot>
%<*quotcirc>
\begin{code}
 S¹ : Type₀
 S¹ = ⊤ / λ _ _ → ⊤
\end{code}
%</quotcirc>
%<*quotient>
\begin{code}
data _/_ (A : Type a) (_~_ : A → A → Type b) : Type (a ℓ⊔ b) where
  [_]    : A → A / _~_
  quot   : ∀ {x y} → x ~ y → [ x ] ≡ [ y ]
  trunc  : isSet (A / _~_)
\end{code}
%</quotient>
%<*circle>
\begin{code}
data S¹ : Type₀ where
  base   : S¹
  loop   : base ≡ base
\end{code}
%</circle>
\begin{code}
_ :
\end{code}
%<*obviously-equal>
\begin{code}
 1 ≡ 1
\end{code}
%</obviously-equal>
\begin{code}
_ = refl
\end{code}
\begin{code}
_ :
\end{code}
%<*obv-add>
\begin{code}
 2 ≡ 1 + 1
\end{code}
%</obv-add>
\begin{code}
_ = refl
\end{code}
%<*trunc-by>
\begin{code}
_on_ : (A → A → B) → (C → A) → C → C → B
_*_ on f = λ x y → f x * f y

TruncBy : (A → B) → Type _
TruncBy {A = A} f = A / (_≡_ on f)
\end{code}
%</trunc-by>
%<*fiber>
\begin{code}
fiber : (A → B) → B → Type _
fiber f y = ∃[ x ] f x ≡ y
\end{code}
%</fiber>
%<*equiv>
\begin{code}
_≃_ : Type a → Type b → Type (a ℓ⊔ b)
A ≃ B =
  Σ[ f ∈ (A → B) ] ∀ x → isContr (fiber f x)
\end{code}
%</equiv>
\begin{code}

infixr 5 _∷_
data List (A : Type a) : Type a where
  [] : List A
  _∷_ : A → List A → List A

map-list : (A → B) → List A → List B
map-list f [] = []
map-list f (x ∷ xs) = f x ∷ map-list f xs

module NoSize where
\end{code}
%<*no-size-tree>
\begin{code}
 infixr 5 _&_
 data Tree (A : Type a) : Type a where
   _&_ : A → List (Tree A) → Tree A
\end{code}%
%</no-size-tree>
\begin{code}
open import Agda.Builtin.Size
\end{code}
%<*sized-tree>
\begin{code}
infixr 5 _&_
data Tree (A : Type a) : Size → Type a where
  _&_ : ∀ {i} → A → List (Tree A i) → Tree A (↑ i)

map-tree : (A → B) → ∀ {i} → Tree A i → Tree B i
map-tree f (x & xs) = f x & map-list (map-tree f) xs
\end{code}
%</sized-tree>
%<*iso>
\begin{code}
record _⇔_  (A : Type a)
            (B : Type b) : Type (a ℓ⊔ b) where
  field
    fun  : A  → B
    inv  : B  → A
    leftInv    : ∀ x → fun  (inv  x) ≡ x
    rightInv   : ∀ x → inv  (fun  x) ≡ x
\end{code}
%</iso>
%<*prop-trunc>
\begin{code}
data ∥_∥ (A : Type a) : Type a where
  ∣_∣ : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y
\end{code}
%</prop-trunc>
\begin{code}
Π : (A : Type a) → (A → Type b) → Type (a ℓ⊔ b)
Π A B =
\end{code}
%<*pi>
\begin{code}
 (x : A) → B x
\end{code}
%</pi>
\begin{code}
Π′ : (A : Type a) → (A → Type b) → Type (a ℓ⊔ b)
Π′ A B =
\end{code}
%<*forall>
\begin{code}
 ∀ x → B x
\end{code}
%</forall>
\begin{code}
sigma : (A : Type a) → (A → Type b) → Type (a ℓ⊔ b)
sigma A B =
\end{code}
%<*sigma>
\begin{code}
 Σ[ x ∈ A ] B x
\end{code}
%</sigma>

\begin{code}
sigma′ : (A : Type a) → (A → Type b) → Type (a ℓ⊔ b)
sigma′ A B =
\end{code}
%<*exists>
\begin{code}
 ∃[ x ] B x
\end{code}
%</exists>
%<*abool>
\begin{code}
a-bool : Bool
a-bool = true
\end{code}
%</abool>
%<*not>
\begin{code}
not : Bool → Bool
not true   = false
not false  = true
\end{code}
%</not>
%<*non-exact-split>
\begin{code}
_⊕_ : ℕ → ℕ → ℕ
zero   ⊕ m     = m
n      ⊕ zero  = n
suc n  ⊕ m     = suc (n ⊕ m)
\end{code}
%</non-exact-split>
%<*unary-inc>
\begin{code}
++_ : ℕ → ℕ
++ n = 1 + n
\end{code}
%</unary-inc>
%<*sum-def>
\begin{code}
data _⊎_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
\end{code}
%</sum-def>
