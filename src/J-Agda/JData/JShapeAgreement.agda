
open import J-Agda.JData.JArray using (Shape ; */)

open import Data.Nat
open import Data.Product
open import Data.Vec using ([] ; _∷_) renaming (take to Vec-take)

open import Relation.Binary using (Rel ; REL)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

import Level

module J-Agda.JData.JShapeAgreement where

ExactShapeAgreement : ∀ {d} → Rel (Shape d) Level.zero
ExactShapeAgreement {d} = _≡_

data PrefixShapeAgreement : ∀ {d₁ d₂} → REL (Shape d₁) (Shape d₂) Level.zero where
  []-prefix  : ∀ {d} → (sh : Shape d) → PrefixShapeAgreement [] sh
  app-prefix : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} → 
               (n : ℕ) → PrefixShapeAgreement sh₁ sh₂ → 
               PrefixShapeAgreement (n ∷ sh₁) (n ∷ sh₂)

{-
PrefixShapeAgreement : ∀ {d₁ d₂} → REL (Shape d₁) (Shape d₂) Level.zero
PrefixShapeAgreement {d₁} {d₂} sh₁ sh₂ = {!Vec-take d₁ sh₂ ≡ sh₁!}
-}