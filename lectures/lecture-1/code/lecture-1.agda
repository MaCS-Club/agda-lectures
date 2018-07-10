module lecture-1 where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc (n + m)

data _even : ℕ → Set where
    ZERO : zero even
    STEP : (x : ℕ) → x even → suc (suc x) even

proof1 : suc (suc (suc (suc zero))) even
proof1 = STEP _ (STEP _ ZERO)


data _∧_ (P : Set) (Q : Set) : Set where
    pair : P → Q → (P ∧ Q)

proof₃ : {P Q : Set} → (P ∧ Q) → P
proof₃  (pair p q) = p

proof₄ : {P Q : Set} → (P ∧ Q) → Q
proof₄  (pair p q) = q

proof₅ : {P Q : Set} → (P ∧ Q) → Q
proof₅  (pair p q) = q

_⇔_ : (P : Set) → (Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)

∧-comm′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm′ (pair p q) = pair q p

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = pair ∧-comm′ ∧-comm′


∧-assoc₁ : { P Q R : Set } → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (pair (pair p q) r) = pair p (pair q r)

∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (pair p (pair q r)) = pair (pair p q) r

∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
∧-assoc = pair ∧-assoc₁ ∧-assoc₂

data _∨_ (P Q : Set) : Set where
   Left : P → P ∨ Q
   Right : Q → P ∨ Q

∨-elim : {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
∨-elim ac bc (Left a) = ac a
∨-elim ac bc (Right b) = bc b

∨-comm′ : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm′ (Left p) = Right p
∨-comm′ (Right q) = Left q

∨-comm : {P Q : Set} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = pair ∨-comm′ ∨-comm′

data ⊥ : Set where

¬ : Set → Set -- for ¬ type \neg
¬ A = A → ⊥
