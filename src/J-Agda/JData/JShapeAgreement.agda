
open import J-Agda.JData.JArray using (Shape ; */)

open import Data.Nat
open import Data.Product
open import Data.Vec
  using ([] ; _∷_)
  renaming (take to Vec-take ; _++_ to _Vec-++_)

open import Relation.Binary using (Rel ; REL)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong)

import Level

module J-Agda.JData.JShapeAgreement where

ExactShapeAgreement : ∀ {d} → Rel (Shape d) Level.zero
ExactShapeAgreement {d} = _≡_

data PrefixShapeAgreement : ∀ {d₁ d₂} →
  REL (Shape d₁) (Shape d₂) Level.zero where
  []-prefix  : ∀ {d} → (sh : Shape d) → PrefixShapeAgreement [] sh
  ∷-prefix : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} → 
               (n : ℕ) → PrefixShapeAgreement sh₁ sh₂ → 
               PrefixShapeAgreement (n ∷ sh₁) (n ∷ sh₂)


lemma-++-ℕ : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} →
  PrefixShapeAgreement sh₁ sh₂ → Σ[ d-rem ∈ ℕ ] d₂ ≡ d₁ + d-rem
lemma-++-ℕ {.0} {d₂} {.[]} {sh₂} ([]-prefix .sh₂) = d₂ , refl
lemma-++-ℕ (∷-prefix n psa) with lemma-++-ℕ psa 
...                         | d-rem , eq = d-rem , cong suc eq