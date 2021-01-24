module Fold where

{-
interface Foldable t where
  foldr : (func : elem -> acc -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl : (func : acc -> elem -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl f z t = foldr (flip (.) . flip f) id t z
-}

id : ∀ {A : Set} (x : A) → A
id x = x

flip : ∀ {A B C : Set} (f : A → B → C) → (B → A → C)
flip f y x = f x y

import Relation.Binary.PropositionalEquality
  as Eq
open Eq
  using (_≡_; refl; trans; sym; cong)

open Eq.≡-Reasoning
  using (begin_; step-≡; _∎)

open import Data.Nat
  using (ℕ; zero; suc; _+_)

data List (A : Set) : Set where
  [] : List A
  _∷_ : ∀ (x : A) (xs : List A) → List A
infixr 5 _∷_

foldl : ∀ {A B : Set} (f : B → A → B) (z : B) (xs : List A) → B
foldl f z [] = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

foldl′ : ∀ {A B : Set} (f : B → A → B) (z : B) (xs : List A) → B
foldl′ {A} {B} f z xs = g xs z where
  g : ∀ (xs : List A) (z : B) → B
  g [] z = z
  g (x ∷ xs) z = g xs (f z x)

foldl″ : ∀ {A B : Set} (f : B → A → B) (z : B) (xs : List A) → B
foldl″ {A} {B} f z xs = g xs z where
  g : ∀ (xs : List A) (z : B) → B
  g [] z = z
  g (x ∷ xs) = λ z → g xs (f z x)

foldr : ∀ {A B : Set} (f : B → A → B) (z : B) (xs : List A) → B
foldr f z [] = z
foldr f z (x ∷ xs) = f (foldr f z xs) x

foldl‴ : ∀ {A B : Set} (f : B → A → B) (z : B) (xs : List A) → B
foldl‴ {A} {B} f z xs = foldr g id xs z where
  g : ∀ (id : B → B) (x : A) (z : B) → B
  g id x z = id (f z x)

rev : ∀ (xs : List ℕ) → List ℕ
rev = foldl (flip _∷_) []

rev′ : ∀ (xs : List ℕ) → List ℕ
rev′ = foldl′ (flip _∷_) []

rev″ : ∀ (xs : List ℕ) → List ℕ
rev″ = foldl″ (flip _∷_) []

rev‴ : ∀ (xs : List ℕ) → List ℕ
rev‴ = foldl‴ (flip _∷_) []

notRev : ∀ (xs : List ℕ) → List ℕ
notRev = foldr (flip _∷_) []

_ : notRev (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
_ = refl

_ : rev (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

_ : rev′ (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

_ : rev″ (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

_ : rev‴ (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
_ = refl

_ : foldl‴ (_+_) 0 (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
_ = refl
