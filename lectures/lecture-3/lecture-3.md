---
author: Igor Fedorov
title: Моноиды и полугруппы
date: July 15 2018
---
## Nat
Вспомним определение натуральных чисел:
```agda
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
```

## Nat
И определение сложения:
```agda
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}
```

## Равенство термов
Введём оператор равенства на термах:
```agda
infix 4 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : { x : A } → x ≡ x
```

## Свойства равенства термов
```agda
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl
```

## Свойства равенства термов
```agda
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = ?
```

## Записи - 1
Создать запись можно используя ключевое слово `record`:
```agda
record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B
```

## Записи - 2
Это определяет новый тип `Pair : Set → Set → Set` и две функции проекции:
```agda
Pair.fst : {A B : Set} → Pair A B → A
Pair.snd : {A B : Set} → Pair A B → B
```

## Записи - 3
Создать элемент данного типа можно:
```agda
p23 : Pair Nat Nat
p23 = record { fst = 2; snd = 3 }
```

## Записи - 4
Или можно ввести конструктор:
```agda
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

p45 : Pair Nat Nat
p45 = 4 , 5
```

## Полугруппы - 1
С помощью записей можем, например, ввести понятие полугруппы:
```agda
record Semigroup (A : Set) (_∘_ : A → A → A) : Set where
  field
    assoc : (a b c : A) → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
```

## Полугруппы - 2
Чтобы доказать, что какое-то множество является полугруппой нужно создать элемент типа `Semigroup` предоставив доказательство ассоциативности:

## Полугруппы - 3
```agda
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero _ _ = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

ℕ+-isSemigroup : Semigroup ℕ _+_
ℕ+-isSemigroup = record
  {
    assoc = +-assoc
  }
```

## Моноиды - 1
Определим и понятие моноида:
```agda
record Monoid (A : Set) (_∘_ : A → A → A) (id : A): Set where
  field
    leftUnit : (a : A) → (id ∘ a) ≡ a
    rightUnit : (a : A) → (a ∘ id) ≡ a
    assoc : (a b c : A) → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
```

## Моноиды - 2
```agda
ℕ+-isMonoid : Monoid ℕ _+_ zero
ℕ+-isMonoid = ?
```

## Свойства списков
```agda
List-isMonoid : {A : Set} → Monoid (List A) _++_ []
List-isMonoid = ?
```
