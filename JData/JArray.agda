module JData.JArray where

open import Data.Nat
open import Data.Fin
  using (Fin ; toℕ) renaming
  (zero to Fin-zero ; suc to Fin-suc)


open import Algebra
open import Data.Nat.Properties

open CommutativeSemiring commutativeSemiring using (*-comm ; +-comm ;  distribʳ)

open import Data.Vec
  hiding
    (lookup)
  renaming
    (head to Vec-head ; tail to Vec-tail ; take to Vec-take ; drop to Vec-drop)

open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning

Shape : ℕ → Set
Shape = Vec ℕ

*/ : ∀ {d} → Shape d → ℕ
*/ [] = 1
*/ (x ∷ sh) = x * */ sh


data JArray (A : Set) : {d : ℕ} → Shape d → Set where
  _ρ́_ : ∀ {d len} → 
        (sh : Shape d) → (xs : Vec A len) → ⦃ prop : len ≡ */ sh ⦄ → 
        JArray A sh

JScalar : Set → Set
JScalar A = JArray A []

mkJScalar : {A : Set} → A → JScalar A
mkJScalar a = [] ρ́ ([ a ])

private
  module _ where
    jtest : JArray ℕ [ 3 ]
    jtest = [ 3 ] ρ́ (0 ∷ 0 ∷ [ 0 ])


private
  module Projections {A : Set} {d : ℕ} {shape : Shape d} where
    shapeVec : JArray A shape → Vec ℕ d
    shapeVec j1 = shape

    flatLen : JArray A shape → ℕ
    flatLen (_ρ́_ .{d} {len} .shape xs ⦃ prop ⦄) = len

    shape-len-prop : (j : JArray A shape) → (flatLen j ≡ */ shape)
    shape-len-prop (_ρ́_ .shape xs ⦃ prop ⦄) = prop

    flatVec : JArray A shape → Vec A (*/ shape)
    flatVec (_ρ́_ .shape xs ⦃ prop ⦄) rewrite prop = xs

    flatVec_withLen_ : JArray A shape → (len : ℕ) → ⦃ prop : */ shape ≡ len ⦄ → Vec A len
    (flatVec j1 withLen len) ⦃ prop ⦄ rewrite sym prop = flatVec j1

    flatVec_with-≡_ : JArray A shape → {len : ℕ} → (prop : */ shape ≡ len) → Vec A len
    flatVec j1 with-≡ prop rewrite sym prop = flatVec j1

    dim : JArray A shape → ℕ
    dim j1 = d

open Projections public

private
  module JMonadicFunctions {A : Set} {d} {sh : Shape d} where -- not to be confused with monads

    head : {n : ℕ} → JArray A (suc n ∷ sh) → JArray A sh
    head j1 = sh ρ́ Vec-take (*/ sh) (flatVec j1)

    tail : {n : ℕ} → JArray A (suc n ∷ sh) → JArray A (n ∷ sh)
    tail {n} j1 = (n ∷ sh) ρ́ Vec-drop (*/ sh) (flatVec j1)

    ,́_ : JArray A sh → JArray A ([ */ sh ])
    ,́ j1 = ([ */ sh ] ρ́ flatVec j1) ⦃ sym (
      begin
        */ sh * 1
      ≡⟨ *-comm (*/ sh) 1 ⟩
        */ sh + 0
      ≡⟨ +-comm (*/ sh) 0 ⟩
        */ sh
      ∎) ⦄

open JMonadicFunctions public


private
  module JDyadicFunctions {A : Set} {d} {sh : Shape d} where

    take : ∀ {n} → (m : ℕ) → JArray A (m + n ∷ sh) → JArray A (m ∷ sh)
    take {n} m j1 = (m ∷ sh) ρ́ Vec-take (m * */ sh)
                    (flatVec j1 with-≡ distribʳ (*/ sh) m n)

    drop : ∀ {n} → (m : ℕ) → JArray A (m + n ∷ sh) → JArray A (n ∷ sh)
    drop {n} m j1 = (n ∷ sh) ρ́ Vec-drop (m * */ sh) 
                    (flatVec j1 with-≡ distribʳ (*/ sh) m n)

    lookup : ∀ {n} → Fin n → JArray A (n ∷ sh) → JArray A sh
    lookup finn j1 = {!!}


open JDyadicFunctions public