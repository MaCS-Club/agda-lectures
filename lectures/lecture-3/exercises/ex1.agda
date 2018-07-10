module ex1 where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

infix 4 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : { x : A } → x ≡ x

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = ?

record Semigroup (A : Set) (_∘_ : A → A → A) : Set where
  field
    assoc : (a b c : A) → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
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

ℕ+-isMonoid : Monoid ℕ _+_ zero
ℕ+-isMonoid = ?

infixr 5 _::_ _++_

data List(A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

List-isMonoid : {A : Set} → Monoid (List A) _++_ []
List-isMonoid = ?
