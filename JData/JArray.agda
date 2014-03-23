module JData.JArray where

open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning

-- helpful definitions
*/ : {n : ℕ} → Vec ℕ n → ℕ
*/ [] = 1
*/ (x ∷ vec) = x * */ vec

Shape : ℕ → Set
Shape = Vec ℕ

-- JArray is a flat vector whose length is the product fold of an
-- associated shape
data JArray (A : Set) : ∀ {r} → (sh : Shape r) → Set where
  jarray : ∀ {r} → (sh : Shape r) → Vec A (*/ sh) → JArray A sh

-- data declarations don't get projections for free
private
  module Dummy (A : Set) {r : ℕ} {s : Shape r} where
    ravel : JArray A s → Vec A (*/ s)
    ravel (jarray .s xs) = xs

    rank : JArray A s → ℕ
    rank j1 = r

    shape : JArray A s → Shape r
    shape j1 = s

open Dummy public

-- */ [] ≡ 1
JScalar : Set → Set
JScalar A = JArray A []

mkJScalar : {A : Set} → A → JScalar A
mkJScalar a = jarray [] ([ a ])

jtest : JScalar ℕ
jtest = mkJScalar 3

_mat+_ : {A B : Set} → {shape : Shape 2} → 
         JArray ℕ shape → JArray ℕ shape → JArray ℕ shape
_mat+_ {shape = s} (jarray .s xs₁) (jarray .s xs₂) = 
       jarray s (zipWith _+_ xs₁ xs₂)