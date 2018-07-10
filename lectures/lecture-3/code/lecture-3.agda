module lecture-3 where

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
sym refl = refl

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

+-rightUnit : (n : ℕ) → (n + zero) ≡ n
+-rightUnit zero = refl
+-rightUnit (suc n) = cong suc (+-rightUnit n)

+-leftUnit : (n : ℕ) → (zero + n) ≡ n
+-leftUnit zero = refl
+-leftUnit (suc n) = cong suc (+-leftUnit n)

ℕ+-isMonoid : Monoid ℕ _+_ zero
ℕ+-isMonoid = record {
    assoc = +-assoc;
    rightUnit = +-rightUnit;
    leftUnit = +-leftUnit
  }

infixr 5 _::_ _++_

data List(A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

List-rightUnit : {A : Set} → (list : List A) → (list ++ []) ≡ list
List-rightUnit [] = refl
List-rightUnit (x :: xs) = cong (λ tail → x :: tail) (List-rightUnit xs)

List-leftUnit : {A : Set} → (list : List A) → ([] ++ list) ≡ list
List-leftUnit [] = refl
List-leftUnit (x :: xs) = cong (λ tail → x :: tail) (List-leftUnit xs)

List-assoc : {A : Set} → (a b c : List A) → (a ++ b) ++ c ≡ a ++ (b ++ c)
List-assoc [] _ _ = refl
List-assoc (x :: a) b c = cong (λ tail → x :: tail) (List-assoc a b c)

List-isMonoid : {A : Set} → Monoid (List A) _++_ []
List-isMonoid = record
  {
    assoc = List-assoc;
    leftUnit = List-leftUnit;
    rightUnit = List-rightUnit
  }
