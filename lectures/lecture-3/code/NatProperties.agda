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
*-leftZero _ = refl

*-rightZero : ∀ n → n * 0 ≡ 0
*-rightZero 0 = refl
*-rightZero (suc a) = *-rightZero a

*-rightUnit : ∀ n → n * 1 ≡ n
*-rightUnit zero = refl
*-rightUnit (suc a) = cong suc (*-rightUnit a)

*-leftUnit : ∀ n → 1 * n ≡ n
*-leftUnit zero = refl
*-leftUnit (suc a) = cong suc (*-leftUnit a)

+-*-suc : ∀ m n → m * suc n ≡ m + m * n
+-*-suc zero _ = refl
+-*-suc (suc m) n = begin
      suc m * suc n         ≡⟨⟩
      suc n + m * suc n     ≡⟨ cong (suc n +_) (+-*-suc m n) ⟩
      suc n + (m + m * n)   ≡⟨⟩
      suc (n + (m + m * n)) ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
      suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
      suc (m + n + m * n)   ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
      suc (m + (n + m * n)) ≡⟨⟩
      suc m + suc m * n     ∎

*-comm : ∀ a b → a * b ≡ b * a
*-comm zero b = sym(*-rightZero b)
*-comm (suc a) b = begin
      suc a * b ≡⟨ cong (b +_) (*-comm a b) ⟩
      b + b * a ≡⟨ sym (+-*-suc b a) ⟩
      b * suc a ∎


*-distr : ∀ a b c  → (a + b) * c ≡ a * c + b * c
*-distr zero _ _ = refl
*-distr (suc a) b c = begin
      (suc a + b) * c ≡⟨⟩
      c + (a + b) * c ≡⟨ cong (c +_) (*-distr a b c) ⟩
      c + (a * c + b * c) ≡⟨ sym (+-assoc c (a * c) (b * c)) ⟩
      c + a * c + b * c ≡⟨⟩
      suc a * c + b * c ∎

*-assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
*-assoc zero _ _ = refl
*-assoc (suc a) b c = begin
      (suc a * b) * c ≡⟨⟩
      (b + a * b) * c ≡⟨ *-distr b (a * b) c ⟩
      b * c + a * b * c ≡⟨ cong (b * c +_) (*-assoc a b c) ⟩
      b * c + a * (b * c) ≡⟨⟩
      suc a * (b * c) ∎

*-distl : ∀ a b c  → a * (b + c) ≡ a * b + a * c
*-distl zero _ _ = refl
*-distl (suc a) b c = begin
      suc a * (b + c) ≡⟨⟩
      b + c + a * (b + c) ≡⟨ cong (b + c +_) (*-distl a b c) ⟩
      b + c + (a * b + a * c) ≡⟨ sym  (+-assoc (b + c) (a * b) (a * c)) ⟩
      b + c + a * b + a * c ≡⟨ cong (λ x → x + a * b + a * c) (+-comm b c) ⟩
      c + b + a * b + a * c ≡⟨ cong (λ x → x + a * c) (+-assoc c b (a * b)) ⟩
      c + (suc a * b) + a * c ≡⟨ cong (λ x → x + a * c) (+-comm c (suc a * b)) ⟩
      suc a * b + c + a * c ≡⟨  +-assoc (suc a * b) c (a * c) ⟩
      suc a * b + suc a * c ∎
