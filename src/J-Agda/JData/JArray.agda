open import Data.Nat
open import Data.Nat.Properties using (n∸n≡0)
open import Data.Fin
  using (Fin ; toℕ)
  renaming (zero to Fin-zero ; suc to Fin-suc)

open import Algebra
open import Data.Nat.Properties

open CommutativeSemiring commutativeSemiring 
  using (*-comm ; +-comm ;  distribʳ ; *-identity)

open import Data.Vec
  hiding (lookup)
  renaming (head to Vec-head ; tail to Vec-tail ; 
            take to Vec-take ; drop to Vec-drop ;
            replicate to Vec-rep ; _++_ to _Vec-++_)

open import Data.Product hiding (map)

open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open PropEq.≡-Reasoning

open import Relation.Binary using (REL)
import Level

open import J-Agda.Util.Properties

module J-Agda.JData.JArray where

open import J-Agda.JData.JShape
open J-Agda.JData.JShape.ShapeAgreement
open import J-Agda.JData.JIndex

data JArray (A : Set) : {d : ℕ} → Shape d → Set where
  shape-bind : ∀ {d len} → (sh : Shape d) → (xs : Vec A len) → 
               ⦃ prop : len ≡ */ sh ⦄ → JArray A sh

JScalar : Set → Set
JScalar A = JArray A []

toJScalar : {A : Set} → A → JScalar A
toJScalar a = shape-bind [] [ a ]

fromJScalar : {A : Set} → JScalar A → A
fromJScalar (shape-bind .[] xs ⦃ prop ⦄ ) rewrite prop = Vec-head xs

open import Data.Vec.N-ary using (N-ary ; curryⁿ)

shape-bind-nary : ∀ {A} {d len} → (sh : Shape d) → ⦃ prop : len ≡ */ sh ⦄ → N-ary len A (JArray A sh)
shape-bind-nary {A = A} {len = len} sh ⦃ prop ⦄ = curryⁿ (λ (xs : Vec A len) → shape-bind sh xs)

private
  module _ where
    jtest : JArray ℕ [ 3 ]
    jtest = shape-bind [ 3 ] (0 ∷ 0 ∷ [ 0 ])

    jtest' : JArray ℕ (2 ∷ [ 3 ])
    jtest' = shape-bind-nary (2 ∷ [ 3 ]) 0 1 2 3 4 5


private
  module Projections {A : Set} {d : ℕ} {sh : Shape d} where
    shapeVec : JArray A sh →  Shape d
    shapeVec j1 = sh

    flatLen : JArray A sh → ℕ
    flatLen (shape-bind .{d} {len} .sh xs) = len

    shape-len-prop : (j : JArray A sh) → (flatLen j ≡ */ sh)
    shape-len-prop (shape-bind .sh xs ⦃ prop ⦄) = prop

    flatVec : JArray A sh → Vec A (*/ sh)
    flatVec (shape-bind .sh xs ⦃ prop ⦄) rewrite prop = xs

    flatVec_withLen_ : JArray A sh → (len : ℕ) → ⦃ prop : */ sh ≡ len ⦄ → Vec A len
    (flatVec j1 withLen len) ⦃ prop ⦄ rewrite sym prop = flatVec j1

    flatVec_with-≡_ : JArray A sh → {len : ℕ} → (prop : */ sh ≡ len) → Vec A len
    flatVec j1 with-≡ prop rewrite sym prop = flatVec j1

    dim : JArray A sh → ℕ
    dim j1 = d

open Projections public

private
  module ShapeRebinds {A : Set} {d} {sh : Shape d} where -- shape substitutions

    shape-rebind : (sh' : Shape d) → JArray A sh → ⦃ prop : sh ≡ sh' ⦄ → 
                JArray A sh'
    (shape-rebind sh' j1) ⦃ prop ⦄ rewrite prop = j1

    shape-rebind₂ : ∀ {d'} → (sh' : Shape d') → JArray A sh →
      ⦃ prop₁ : d ≡ d' ⦄ → ⦃ prop₂ : subst Shape prop₁ sh ≡ sh' ⦄ →  JArray A sh'
    shape-rebind₂ sh' j ⦃ refl ⦄ ⦃ prop₂ ⦄ rewrite prop₂ = j


open ShapeRebinds public

private
  module JUnaryFunctions {A : Set} {d} {sh : Shape d} where

    head : {n : ℕ} → JArray A (suc n ∷ sh) → JArray A sh
    head j1 = shape-bind sh (Vec-take (*/ sh) (flatVec j1))

    tail : {n : ℕ} → JArray A (suc n ∷ sh) → JArray A (n ∷ sh)
    tail {n} j1 = shape-bind (n ∷ sh) (Vec-drop (*/ sh) (flatVec j1))

    ravel : JArray A sh → JArray A ([ */ sh ])
    ravel (shape-bind .sh xs ⦃ prop ⦄) rewrite prop = 
          (shape-bind [ */ sh ] xs) ⦃ sym (proj₂ *-identity (*/ sh)) ⦄

    itemize : JArray A sh → JArray A (1 ∷ sh)
    itemize (shape-bind .sh xs ⦃ prop ⦄ ) rewrite prop =
      shape-bind (1 ∷ sh) xs ⦃ sym (proj₁ *-identity (*/ sh)) ⦄

open JUnaryFunctions public


private
  module JBinaryFunctions {A : Set} {d} {sh : Shape d} where

    take : ∀ {n} → (m : ℕ) → JArray A (m + n ∷ sh) → JArray A (m ∷ sh)
    take {n} m j = shape-bind (m ∷ sh) (Vec-take (m * */ sh)
                    (flatVec j with-≡ distribʳ (*/ sh) m n))

    drop : ∀ {n} → (m : ℕ) → JArray A (m + n ∷ sh) → JArray A (n ∷ sh)
    drop {n} m j = shape-bind (n ∷ sh) (Vec-drop (m * */ sh) 
                    (flatVec j with-≡ distribʳ (*/ sh) m n))

    lookup : ∀ {n} → Fin n → JArray A (n ∷ sh) → JArray A sh
    lookup {n} finn j with lemma-Fin-to-sum finn 
    ...               | k , fn+sk≡n =
      let j' = (shape-rebind (toℕ finn + suc k ∷ sh) j)
                ⦃ cong (λ x → x ∷ sh) (sym fn+sk≡n) ⦄
      in head (drop (toℕ finn) j')

    _++_ : ∀ {s s'} → JArray A (s ∷ sh) → JArray A (s' ∷ sh) → JArray A (s + s' ∷ sh)
    _++_ {s} {s'} j k = shape-bind (s + s' ∷ sh) (flatVec j Vec-++ flatVec k)
                        ⦃ sym (distribʳ (*/ sh) s s') ⦄

    replicate-scalar : A → JArray A sh
    replicate-scalar a = shape-bind sh (Vec-rep a)

    replicate : ∀ {d'} → (sh' : Shape d') → JArray A sh → JArray A (sh' Vec-++ sh)
    replicate [] j = j
    replicate (s ∷ sh') j with Vec-rep {n = s} (replicate sh' j)
    ...                   | rep-rec = shape-bind (s ∷ sh' Vec-++ sh) (concat (map flatVec rep-rec))


open JBinaryFunctions public

private
  module JIndexedFunctions {A : Set} where

    lookup-scalar : ∀ {d} → {sh : Shape d} → JIndex sh → JArray A sh → A
    lookup-scalar []i j = fromJScalar j
    lookup-scalar (x ∷i idx) j = lookup-scalar idx (lookup x j)

    lookup-index : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} → 
      (pre : Prefix sh₁ sh₂) → JIndex sh₁ → JArray A sh₂ → JArray A (suffix pre)
    lookup-index {sh₂ = sh₂} ([]-pref .sh₂) []i j = j
    lookup-index (∷-pref .n pre) (_∷i_ {n} x idx) j =
                 lookup-index pre idx (lookup x j)

    lookup-scalar' : ∀ {d} → {sh : Shape d} → JIndex sh → JArray A sh → A
    lookup-scalar' {d = d} {sh = sh} idx j =
      let self-pre = self-prefix sh in
        fromJScalar ((shape-rebind₂ [] (lookup-index self-pre idx j))
          ⦃ self-suffix-len≡0 ⦄ ⦃ self-suffix≡[] ⦄ )

open JIndexedFunctions public


pointwise-map₁ : {A B : Set} → ∀ {d} → {sh : Shape d} →
                 (A → B) → JArray A sh → JArray B sh
pointwise-map₁ f (shape-bind sh xs) = shape-bind sh (map f xs)

indices : ∀ {d} → (sh : Shape d) → JArray (Fin (*/ sh)) sh
indices sh = shape-bind sh (tabulate (λ z → z))

integers : ∀ {d} → (sh : Shape d) → JArray ℕ sh
integers sh = pointwise-map₁ toℕ (indices sh)