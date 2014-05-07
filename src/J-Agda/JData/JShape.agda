open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Nat
open import Data.Product

open import Relation.Binary using (Rel ; REL)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
open import Relation.Nullary

import Level

module J-Agda.JData.JShape where

Shape : ℕ → Set
Shape = Vec ℕ

*/ : ∀ {d} → Shape d → ℕ
*/ [] = 1
*/ (x ∷ sh) = x * */ sh

module ShapeAgreement where

    ExactShapeAgreement : ∀ {d} → Rel (Shape d) Level.zero
    ExactShapeAgreement {d} = _≡_

    data Prefix : ∀ {d₁ d₂} → REL (Shape d₁) (Shape d₂) Level.zero where
      []-pref : ∀ {d} → (sh : Shape d) → Prefix [] sh
      ∷-pref  : ∀ {d₁ d₂} → (s : ℕ) → {sh₁ : Shape d₁} → {sh₂ : Shape d₂}
                → Prefix sh₁ sh₂ → Prefix (s ∷ sh₁) (s ∷ sh₂)

-- get the suffix (needs to be wrapped in a Σ)
    shape-suffix : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} → 
                   Prefix sh₁ sh₂ → Σ[ d-suf ∈ ℕ ] Shape d-suf
    shape-suffix {.0} {d₂} {.[]} {sh₂} ([]-pref .sh₂) = d₂ , sh₂
    shape-suffix (∷-pref s pref) = shape-suffix pref

-- helper function to unwrap a Prefix by the head argument
    pref-pred : ∀ {d₁ d₂ s} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂}
                → Prefix (s ∷ sh₁) (s ∷ sh₂) → Prefix sh₁ sh₂
    pref-pred {d₁} {d₂} {s} (∷-pref .s pr) = pr

-- Prefix is decidable
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


    self-prefix : ∀ {d} → (sh : Shape d) → Prefix sh sh
    self-prefix [] = []-pref []
    self-prefix (x ∷ sh) = ∷-pref x (self-prefix sh)