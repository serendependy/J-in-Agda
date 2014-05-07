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

open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning

open import J-Agda.Util.Properties

module J-Agda.JData.JArray where

open import J-Agda.JData.JShape
open J-Agda.JData.JShape.ShapeAgreement
open import J-Agda.JData.JIndex

data JArray (A : Set) : {d : ℕ} → Shape d → Set where
  _ρ́_ : ∀ {d len} → 
        (sh : Shape d) → (xs : Vec A len) → ⦃ prop : len ≡ */ sh ⦄ → 
        JArray A sh

JScalar : Set → Set
JScalar A = JArray A []

toJScalar : {A : Set} → A → JScalar A
toJScalar a = [] ρ́ ([ a ])

fromJScalar : {A : Set} → JScalar A → A
fromJScalar (_ρ́_ .[] xs ⦃ prop ⦄ ) rewrite prop = Vec-head xs

private
  module _ where
    jtest : JArray ℕ [ 3 ]
    jtest = [ 3 ] ρ́ (0 ∷ 0 ∷ [ 0 ])


private
  module Projections {A : Set} {d : ℕ} {shape : Shape d} where
    shapeVec : JArray A shape →  Shape d
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

    _ρ́-rebind_ : (sh' : Shape d) → JArray A sh → ⦃ prop : sh ≡ sh' ⦄ → 
                JArray A sh'
    (sh' ρ́-rebind j1) ⦃ prop ⦄ rewrite prop = j1

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
    lookup {n} finn j1 with lemma-Fin-to-sum finn 
    ...                | k , fn+sk≡n =
      let j1' = ((toℕ finn + suc k ∷ sh) ρ́-rebind j1)
                ⦃ cong (λ x → x ∷ sh) (sym fn+sk≡n) ⦄
      in head (drop (toℕ finn) j1')

open JDyadicFunctions public

private
  module JIndexedFunctions {A : Set} where

    lookup-scalar : ∀ {d} → {sh : Shape d} → JIndex sh → JArray A sh → A
    lookup-scalar []i j = fromJScalar j
    lookup-scalar (x ∷i idx) j = lookup-scalar idx (lookup x j)

    lookup-index : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} → 
                   (pre : Prefix sh₁ sh₂) → JIndex sh₁ → JArray A sh₂ → JArray A (proj₂ (shape-suffix pre))
    lookup-index {sh₂ = sh₂} ([]-pref .sh₂) []i j = j
    lookup-index (∷-pref .n pre) (_∷i_ {n} x idx) j = lookup-index pre idx (lookup x j)

{-
    lookup-scalar' :  ∀ {d} → {sh : Shape d} → JIndex sh → JArray A sh → A
    lookup-scalar' idx j = fromJScalar (lookup-index {!self-prefix (shapeVec j)!} idx j)
-}

open JIndexedFunctions public