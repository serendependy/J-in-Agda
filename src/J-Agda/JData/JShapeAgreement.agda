
open import J-Agda.JData.JArray using (Shape ; */)

open import Data.Nat
open import Data.Product
open import Data.Vec
  using ([] ; _∷_ ; _∷ʳ_)
  renaming (take to Vec-take ; _++_ to _Vec-++_)

open import Relation.Binary using (Rel ; REL)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong)
open import Relation.Nullary


import Level

module J-Agda.JData.JShapeAgreement where

ExactShapeAgreement : ∀ {d} → Rel (Shape d) Level.zero
ExactShapeAgreement {d} = _≡_

data Prefix : ∀ {d₁ d₂} → REL (Shape d₁) (Shape d₂) Level.zero where
  []-pref : ∀ {d} → (sh : Shape d) → Prefix [] sh
  ∷-pref  : ∀ {d₁ d₂} → (s : ℕ) → {sh₁ : Shape d₁} → {sh₂ : Shape d₂}
            → Prefix sh₁ sh₂ → Prefix (s ∷ sh₁) (s ∷ sh₂)

pref-pred : ∀ {d₁ d₂ s} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂}
            → Prefix (s ∷ sh₁) (s ∷ sh₂) → Prefix sh₁ sh₂
pref-pred {d₁} {d₂} {s} (∷-pref .s pr) = pr

prefix? : ∀ {d₁ d₂} → (sh₁ : Shape d₁) → (sh₂ : Shape d₂) → Dec (Prefix sh₁ sh₂)
prefix? [] sh₂ = yes ([]-pref sh₂)
prefix? (x ∷ sh₁) [] = no (λ ())
prefix? (x ∷ sh₁) (x₁ ∷ sh₂)   with x ≟ x₁ | prefix? sh₁ sh₂ 
prefix? (.x₁ ∷ sh₁) (x₁ ∷ sh₂) | yes refl  | yes p = yes (∷-pref x₁ p)
prefix? (.x₁ ∷ sh₁) (x₁ ∷ sh₂) | yes refl  | no ¬p = no (λ p∷ → ¬p (pref-pred p∷))
prefix? (x ∷ sh₁) (x₁ ∷ sh₂)   | no ¬p     | pr = no (λ p∷ → ¬p (lemma p∷))
  where
    lemma : ∀ {x₁ x₂} → Prefix (x₁ ∷ sh₁) (x₂ ∷ sh₂) → x₁ ≡ x₂
    lemma {.x₂} {x₂} (∷-pref .x₂ pr₁) = refl