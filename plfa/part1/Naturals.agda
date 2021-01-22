module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ 
    suc (1 + 3)
  ≡⟨⟩ 
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 ^ (suc 3)
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ = 
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

_#_ : ℕ → ℕ → ℕ
zero # n = n
suc m # n = suc (m # n)

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = inc x O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

_ : to 3 ≡ ⟨⟩ I I
_ = refl

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * from x
from (x I) = 1 + (2 * from x)

_ : from (⟨⟩ I I O O) ≡ 12
_ = refl

_ : from (⟨⟩ I I I) ≡ 7
_ = refl
