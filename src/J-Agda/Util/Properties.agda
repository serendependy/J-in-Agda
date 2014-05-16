open import Algebra
open import Algebra.FunctionProperties
  using (Op₁ ; Op₂ ; Commutative)

open import Data.Nat
open import Data.Nat.Properties

open CommutativeSemiring commutativeSemiring using (+-comm)

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Props using (prop-toℕ-≤)

open import Data.Product
open import Data.Empty

open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning

module J-Agda.Util.Properties where

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

lemma-≤-to-sum : ∀ {m n} → m ≤ n → Σ[ l ∈ ℕ ] m + l ≡ n
lemma-≤-to-sum {m} {n} ineq with compare m n
lemma-≤-to-sum {m} ineq                  | less .m n = suc n , m+1+n≡1+m+n m n
lemma-≤-to-sum {.n} {n} ineq             | equal .n = 0 , +-comm n zero
lemma-≤-to-sum {.(suc (n + k))} {n} ineq | greater .n k = ⊥-elim (obvious ineq)
  where
    obvious : ∀ {a b} → suc (a + b) ≤ a → ⊥
    obvious {zero} ()
    obvious {suc a} (s≤s ineq₁) = obvious ineq₁

lemma-Fin-to-sum : ∀ {n} → (fn : Fin n) → Σ[ l ∈ ℕ ] toℕ fn + (suc l) ≡ n
lemma-Fin-to-sum {zero} ()
lemma-Fin-to-sum {suc n'} fn with lemma-≤-to-sum (prop-toℕ-≤ fn)
...                      | l , fn+l≡n' = 
                         l , trans (m+1+n≡1+m+n (toℕ fn) l) (cong suc fn+l≡n')

module FoldProps {A : Set} (_·_ : Op₂ A) where
  