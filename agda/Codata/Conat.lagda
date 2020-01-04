\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Conat where

open import Codata.Size
open import Codata.Thunk
open import Prelude
open import Relation.Nullary
\end{code}
%<*def>
\begin{code}
data Conat (i : Size) : Type₀ where
  zero : Conat i
  suc  : Thunk Conat i → Conat i
\end{code}
%</def>
%<*inf>
\begin{code}
inf : ∀ {i} → Conat i
inf = fix Conat suc
\end{code}
%</inf>
\begin{code}
ℕtoConat : ℕ → Conat i
ℕtoConat zero = zero
ℕtoConat (suc n) = suc (λ where .force → ℕtoConat n)

infix 4 _ℕ≤_ _ℕ<_ _ℕ≤?_
data _ℕ≤_ : ℕ → Conat ∞ → Type₀ where
  z≤n : ∀ {n} → zero ℕ≤ n
  s≤s : ∀ {m n} → m ℕ≤ n .force → suc m ℕ≤ suc n

_ℕ<_ : ℕ → Conat ∞ → Type₀
n ℕ< m = suc n ℕ≤ m

p≤p : ∀ {n m} → suc n ℕ≤ suc m → n ℕ≤ m .force
p≤p (s≤s n≤m) = n≤m

_ℕ≤?_ : ∀ m n → Dec (m ℕ≤ n)
zero  ℕ≤? n = yes z≤n
suc m ℕ≤? zero = no (λ ())
suc m ℕ≤? suc n with (m ℕ≤? n .force)
(suc m ℕ≤? suc n) | yes p = yes (s≤s p)
(suc m ℕ≤? suc n) | no ¬p = no (¬p ∘ p≤p)
\end{code}
%<*finite>
\begin{code}
infix 4 _ℕ≋_
_ℕ≋_ : ℕ → Conat ∞ → Type₀
zero   ℕ≋ zero   = ⊤
zero   ℕ≋ suc x  = ⊥
suc n  ℕ≋ zero   = ⊥
suc n  ℕ≋ suc m  = n ℕ≋ m .force

Finite : Conat ∞ → Type₀
Finite n = ∃[ m ] m ℕ≋ n

fin-zero : Finite zero
fin-zero = zero , tt

fin-suc : ∀ {n} → Finite (n .force) → Finite (suc n)
fin-suc (n , p) = (suc n , p)
\end{code}
%</finite>
\begin{code}
¬∄nℕ≋∞ : ∀ n → ¬ (n ℕ≋ inf)
¬∄nℕ≋∞ (suc n) = ¬∄nℕ≋∞ n

¬Fin⟨∞⟩ : ¬ Finite inf
¬Fin⟨∞⟩ = uncurry ¬∄nℕ≋∞

isProp-≋ : ∀ {n m} → isProp (n ℕ≋ m)
isProp-≋ {zero} {zero} tt tt _ = tt
isProp-≋ {suc n} {suc m} n≋m = isProp-≋ {n} {m .force} n≋m

isProp-finite : ∀ {n} → isProp (Finite n)
isProp-finite {zero} (zero , tt) (zero , tt) _ = zero , tt
isProp-finite {suc x} (suc m , p) (suc l , q) i =
  let j , p′ = isProp-finite {x .force} (m , p) (l , q) i
  in suc j , p′

conatToℕ : ∀ {n} → Finite n → ℕ
conatToℕ = fst

toDepth : ℕ → ∀ n → Maybe (Finite n)
toDepth zero    m = nothing
toDepth (suc n) zero = just (zero , tt)
toDepth (suc n) (suc x) with toDepth n (x .force)
toDepth (suc n) (suc x) | nothing = nothing
toDepth (suc n) (suc x) | just  y = just (fin-suc y)

_+_ : Conat i → Conat ∞ → Conat i
zero + y = y
suc x + y = suc λ where .force → (x .force + y)
\end{code}
