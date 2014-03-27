open import Data.Nat

open import Algebra
open import Data.Nat.Properties

open CommutativeSemiring commutativeSemiring using (*-comm ; +-comm)

module JData.JArray where

open import Data.Vec renaming
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

    flatVec : JArray A shape → Vec A (*/ shape)
    flatVec (_ρ́_ .shape xs ⦃ prop ⦄) rewrite prop = xs

    dim : JArray A shape → ℕ
    dim j1 = d

open Projections public

private
  module JMonadicFunctions {A : Set} {d} {sh : Shape d} where -- not to be confused with monads
    --open isCommutativeSemiring

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
    