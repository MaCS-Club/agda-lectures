---
author: Igor Fedorov
title: Свойства натуральных чисел
date: August ?? 2018
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
