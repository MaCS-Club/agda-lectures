module ex1 where

open import Nat
open import PropositionalEquality { ℕ }

record Semigroup (A : Set) (_∘_ : A → A → A) : Set where
  field
    assoc : (a b c : A) → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero _ _ = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

ℕ+-isSemigroup : Semigroup ℕ _+_
ℕ+-isSemigroup = record
  {
    assoc = +-assoc
  }


record Monoid (A : Set) (_∘_ : A → A → A) (id : A): Set where
  field
    leftUnit : (a : A) → (id ∘ a) ≡ a
    rightUnit : (a : A) → (a ∘ id) ≡ a
    assoc : (a b c : A) → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)

+-rightUnit : ∀ a → (a + zero) ≡ a
+-rightUnit = ?

+-leftUnit : ∀ a → (zero + a) ≡ a
+-leftUnit = ?

ℕ+-isMonoid : Monoid ℕ _+_ zero
ℕ+-isMonoid = ?


+-suc : ∀ m n → (suc m + n) ≡ (m + suc n)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero b = sym(+-rightUnit b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (+-suc b a)

+-comm` : ∀ a b → a + b ≡ b + a
+-comm` zero b = sym(+-rightUnit b)
+-comm` (suc a) b = begin
    suc a + b   ≡⟨⟩
    suc (a + b) ≡⟨ cong suc (+-comm a b) ⟩
    suc (b + a) ≡⟨⟩
    suc b + a   ≡⟨ +-suc b a ⟩
    b + suc a   ∎

*-leftZero : ∀ n → 0 * n ≡ 0
*-leftZero = ?

*-rightZero : ∀ n → n * 0 ≡ 0
*-rightZero = ?

*-rightUnit : ∀ n → n * 1 ≡ n
*-rightUnit = ?

*-leftUnit : ∀ n → 1 * n ≡ n
*-leftUnit = ?

+-*-suc : ∀ m n → m * suc n ≡ m + m * n
+-*-suc = ?

*-comm : ∀ a b → a * b ≡ b * a
*-comm = ?


*-distr : ∀ a b c  → (a + b) * c ≡ a * c + b * c
*-distr = ?

*-assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
*-assoc = ?

*-distl : ∀ a b c  → a * (b + c) ≡ a * b + a * c
*-distl = ?
