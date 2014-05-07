open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Nat
open import Data.Product

open import Relation.Binary using (Rel ; REL)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; subst)
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

-- prefix agreement
    data Prefix : ∀ {d₁ d₂} → REL (Shape d₁) (Shape d₂) Level.zero where
      []-pref : ∀ {d} → (sh : Shape d) → Prefix [] sh
      ∷-pref  : ∀ {d₁ d₂} → (s : ℕ) → {sh₁ : Shape d₁} → {sh₂ : Shape d₂}
                → Prefix sh₁ sh₂ → Prefix (s ∷ sh₁) (s ∷ sh₂)

-- self is prefix
    self-prefix : ∀ {d} → (sh : Shape d) → Prefix sh sh
    self-prefix [] = []-pref []
    self-prefix (x ∷ sh) = ∷-pref x (self-prefix sh)


-- Suffix (needs to be wrapped in a Σ)
    mkSuffix : ∀ {d₁ d₂} → {sh₁ : Shape d₁} → {sh₂ : Shape d₂} → 
                   Prefix sh₁ sh₂ → Σ[ d-suf ∈ ℕ ] Shape d-suf
    mkSuffix {.0} {d₂} {.[]} {sh₂} ([]-pref .sh₂) = d₂ , sh₂
    mkSuffix (∷-pref s pref) = mkSuffix pref

-- helper projections of suffix
    private
      module Suffix {d₁ d₂ : ℕ} {sh₁ : Shape d₁} {sh₂ : Shape d₂} where

        suffix-len : (pre : Prefix sh₁ sh₂) → ℕ
        suffix-len pre = proj₁ (mkSuffix pre)

        suffix : (pre : Prefix sh₁ sh₂) → Shape (suffix-len pre)
        suffix pre = proj₂ (mkSuffix pre)

    open Suffix public

-- properties of suffix
    self-suff-len≡0 : ∀ {d} → {sh : Shape d} → (pre : Prefix sh sh) → suffix-len pre ≡ 0
    self-suff-len≡0 ([]-pref .[]) = refl
    self-suff-len≡0 (∷-pref s pre) = self-suff-len≡0 pre

    self-suff≡[] : ∀ {d} → {sh : Shape d} → (pre : Prefix sh sh) → subst Shape (self-suff-len≡0 pre) (suffix pre) ≡ []
    self-suff≡[] ([]-pref .[]) = refl
    self-suff≡[] (∷-pref s pre) = self-suff≡[] pre


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