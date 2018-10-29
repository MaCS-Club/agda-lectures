---
author: Igor Fedorov
title: Введение в HoTT и CubicalTT
---

# Пути в топологии

##

В топологическом пространстве `X` путём из `a` в `b` называется непрерывное отображение `f` из интервала `[0,1]` в `X` такое, что `f(0) = a` и `f(1) = b`.

##

В топологическом пространстве `X` путём из `a` в `b` называется непрерывное отображение `f` из интервала `[0,1]` в `X` такое, что `f(0) = a` и `f(1) = b`.

Если существует путь из `a` в `b`, то существует и путь из `b` в `a`.

##

В топологическом пространстве `X` путём из `a` в `b` называется непрерывное отображение `f` из интервала `[0,1]` в `X` такое, что `f(0) = a` и `f(1) = b`.

Если существует путь из `a` в `b`, то существует и путь из `b` в `a`.

Если существует путь из `a` в `b` и из `b` в `c`, то существует их композиция т.е. путь из `a` в `c`.

##

Непрерывное отображение `f : [0,1] x X → Y` называется гомотопией.

##

Имея два пути `p` и `q` мы можем так же рассмотреть непрерывное отображение одного пути в другой, это будет непрерывное отображение `[0,1]` в пространство путей или, что то же самое, отображение `[0,1] x [0,1]` в исходное топологическое пространстве т.е. будет являться гомотопией.

Так же мы можем рассмотреть пути в пространстве путей между путями, которые тоже будут являться гомотопиями и так далее.

##

Любое топологическое пространство `X` является категорией, объектами которой являются точки `X`, а морфизмами являются классы путей. Поскольку любой морфизм в этой категории является изоморфизмом, эта категория является группоидом, так называемым фундаментальным группоидом `X`. Группа автоморфизмов точки `x` в `X` — это просто фундаментальная группа в `X`.

##

Группоид в котором рассматривается бесконечная башня морфизмов между морфизмами, т.е. для любого объекта на любом уровне множество его изоморфизмов обладает структурой группоида, называется ∞-группоидом.

# Identity types это пути

##

Если рассмотреть введённый нами ранее типы `_≡_` то можно увидеть, что они ведут себя как пути в топологии!

##

Более того, если `p q : x ≡ y` т.е. являются док-вом равенства `x` и `y`, то утверждение об их равенстве будет иметь тип `p ≡ q` и так до бесконечности т.е. имеют структуру ∞-группоида.

# CubicalTT

##

Кубическая теория типов это расширение теории типов позволяющее напрямую работать с n-мерными кубами(точка, линия, квадрат, куб и т.д.).
Она предлагает новый способ рассуждения о типах тождественности, например, в данной теории доказуема функциональная эктенсиональность и аксиома унивалентности Воеводского.

##

На данном этапе есть экспериментальный компилятор `mortberg/cubicaltt` и в Agda с версии 2.6.0(не выпущена) ест директива `{-# OPTIONS --cubical #-}`.

## Тип интервала

В кубической теории типов вводится тип интервала `I`, который топологически соответствует единичному интервалу. В ограниченном контексте этот тип имеет всего два значения начало `i0` и конец `i0`

```agda
a b : I
a = i0
b = i1
```

##

Элементы интервала имеют вид алгебры де Моргана:

```agda
max = i ∨ j
min = i ∧ j
neg = ~ i
```

##

Для типа интервала выполняются все свойства алгебры де Моргана :

```agda
p₁ : i0 ∨ i    ≡ i
p₂ : i  ∨ i1   ≡ i1
p₃ : i  ∨ j    ≡ j ∨ i
p₄ : i  ∧ j    ≡ j ∧ i
p₅ : ~ (~ i)   ≡ i
p₆ : i0        ≡ ~ i1
p₇ : ~ (i ∨ j) ≡ ~ i ∧ ~ j
p₈ : ~ (i ∧ j) ≡ ~ i ∨ ~ j
```

## Тип пути

Зависимый тип пути(путь между путями):

```agda
PathP : ∀ {α} (A : I → Set α) → A i0 → A i1 → Set α
```

##

Не зависимый путь:

```agda
Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b
```

##

Тип тождественности можно переписать так:

```agda
_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ _ → A)
```

##

Тогда рефлексивность можно пеерписать как:

```agda
refl : {x : A} → x ≡ x
refl {x = x} = λ _ → x
```

##

Симметричность:

```agda
sym : {x y : A} → x ≡ y → y ≡ x
sym p = ?
```


##

Симметричность:

```agda
sym : {x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (~ i)
```

##

Конгруентность:

```agda
cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong f p = λ i → f (p i)
```