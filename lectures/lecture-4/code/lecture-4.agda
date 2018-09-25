module lecture-4 where

open import Agda.Primitive
open import Data.Nat hiding (_⊔_)

const : ∀ { n m }{ A : Set n } (B : Set m) → (x : A) → Set m
const = λ B x → B

-- f : ℕ → Set _
-- f = const Set₂


-- \lub максимум
Π : ∀ { n m }(A : Set n)(B : A → Set m) → Set(m ⊔ n) -- \Pi
Π A B = (x : A) → B x


g : Π ℕ (const ℕ)
g x = x + 1

id : Π Set (λ z → (x : z) → z)
-- id : (A : Set) → A → A
id = λ(A : Set)(x : A) → x


record Σ {i j} (A : Set i) (P : A → Set j) : Set (i ⊔ j) where  -- \Sigma
  constructor _,_
  field
    π₁ : A       -- \pi\_1
    π₂ : P (π₁)  -- \pi\_2

_×_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)  -- \times
A × B = Σ A (const B)

pair : ∀ {A B : Set} → A → B → A × B
pair a b = record
  {
    π₁ = a;
    π₂ = b
  }

infixr 1 _⊎_ -- \u+

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B
