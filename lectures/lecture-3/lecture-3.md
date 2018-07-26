---
author: Igor Fedorov
title: Свойства ℕ
date: July 22 2018
---

## Модули

##

В _agda_ импортировать код из другого модуля можно:
```agda
import M
```
После этого можно использовать определённые в `M` сущности через `M.`, например `M.f` для того, чтобы вызвать функцию `f` из модуля `M`

## Модули - 2

Для того, чтобы использовать сущности без явного указания названия модуля:
```agda
open import M
```
или
```agda
import M
open M
```

## Модули - 3

Для импортируемых модулей можно задавать алиасы, указывать какие сущности импортировать, а какие наоборот скрывать. У модулей так же могут быть явные и не явные параметры.

Обо всём об этом можно почитать, например, на [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Modules)

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

## Свойства равенства термов - 2
```agda
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = ?
```

## Свойства равенства термов - 3
```agda
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
```

## Свойства равенства термов - 3  

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = ?

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
p23 : Pair ℕ ℕ
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

p45 : Pair ℕ ℕ
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

## Удобный синтаксис для доказательства равенств

##

Для того, чтобы было проще доказывать равенства термов мы можем ввести дополнительные функции позволяющие писать в более удобном синтаксисе:

##

```agda
infix  3 _∎
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  1 begin_
```
```agda
begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl
```

## Коммутативность сложения

##

 Для примера возьмём доказательство коммутативности сложения
```agda
+-suc : ∀ m n → (suc m + n) ≡ (m + suc n)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)
```
```agda
+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym(+-rightUnit b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (+-suc b a)
```

##

И перепишем с использованием нового синтаксиса
```agda
+-suc : ∀ m n → (suc m + n) ≡ (m + suc n)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)
```
```agda
+-comm` : ∀ a b → a + b ≡ b + a
+-comm` zero b = sym(+-rightUnit b)
+-comm` (suc a) b = begin
    suc a + b   ≡⟨⟩
    suc (a + b) ≡⟨ cong suc (+-comm a b) ⟩
    suc (b + a) ≡⟨⟩
    suc b + a   ≡⟨ +-suc b a ⟩
    b + suc a   ∎
```
