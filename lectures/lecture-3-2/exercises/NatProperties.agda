module NatProperties where

open import Nat
open import PropositionalEquality { ℕ }

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero _ _ = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-leftUnit : (n : ℕ) → (zero + n) ≡ n
+-leftUnit m = refl

+-rightUnit : (n : ℕ) → (n + zero) ≡ n
+-rightUnit zero = refl
+-rightUnit (suc n) = cong suc (+-rightUnit n)

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
