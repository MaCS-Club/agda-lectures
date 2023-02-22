module lecture-2 where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

infixr 4 _::_

data List(A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

empty : List ℕ
empty = []

upto3 : List ℕ
upto3 = 0 :: 1 :: 2 :: 3 :: []

append : ∀ {A} → List A → List A → List A
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

data Option(A : Set) : Set where
  Some : A → Option A
  None : Option A

first : ∀ {A} → List A → Option A
first [] = None
first (x :: _) = Some x

data Vec(A : Set) : ℕ → Set where
  [] : Vec A 0
  _::_ : ∀ {n} → A → Vec A n → Vec A (1 + n)

emptyV : Vec ℕ 0
emptyV = []

upto3V : Vec ℕ 4
upto3V = 0 :: 1 :: 2 :: 3 :: []

appendV : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
appendV [] ys = ys
appendV (x :: xs) ys = x :: appendV xs ys

firstV : ∀ {A n} → Vec A (1 + n) → A
firstV (x :: _) = x

data ℕ< : ℕ → Set where
  zero : ∀ {n} → ℕ< (1 + n)
  1+ : ∀ {n} → ℕ< n → ℕ< (1 + n)


three : ℕ< 7
three = 1+ (1+ (1+ zero))

three' : ℕ< 10
three' = 1+ (1+ (1+ zero))

_!_ : ∀ {A n} → Vec A n → ℕ< n → A
(x :: _) ! zero = x
(_ :: xs) ! (1+ m) = xs ! m

one = upto3V ! (1+ zero)
-- out-of-bounds = upto3V ! (1+ (1+ (1+ (1+ zero))))
