open import J-Agda.JData.JShape

open import Data.Fin
open import Data.Vec
  using ([] ; _∷_)

module J-Agda.JData.JIndex where

data JIndex : ∀{d} → Shape d → Set where
  []i  : JIndex []
  _∷i_ : ∀ {n d} → {sh : Shape d} → Fin n → JIndex sh → JIndex (n ∷ sh)