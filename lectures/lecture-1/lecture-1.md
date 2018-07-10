---
author: Igor Fedorov
title: Соответствие Карри-Говарда
date: February 25 2018
---

## Соответствие Карри-Говарда

Соответствие Карри-Говарда устанавливает соответствие между типизированным лямбда исчислением и интуиционистской логикой.

##

Типы соответствуют высказываниям. Если мы построим значение определённого типа, то мы так же докажем высказываение соответствующее этому типу.

Поскольку типы являются высказываниям, а значения являются доказательствами, конструкторы для типа соответствуют правилам вывода для соответствующего предположения.

##

Для примера закодируем чётные натуральные числа:

```agda
data _even : ℕ → Set where
    ZERO : zero even
    STEP : (x : ℕ) → x even → suc (suc x) even
    --вместо (x : ℕ) можно использовать ∀ x
```

##

Теперь докажем, что четвёрка является чётным числом. Нам нужно доказать обитаемость типа `suc (suc (suc (suc zero))) even`, для этого воспользуемся помощью agda-mode, напишем:

```agda
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = ?
```

##

Используя agda-mode выполним команду `load`, которая "загрузит" наш файл, после чего вопросик заменится на так называемую _дырку_:

```agda
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = {!   !}
```

##

После этого выполним команду `auto`, которая автоматически подберёт нужный терм:

```agda
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)
```

## Читайте документацию

В agda-mode есть ещё множество полезных команд помогающих интерактивно работать с кодом на Agda, все их можно посмотреть в документации на официальном сайте.

## Имплиситы

##

В нашем доказательстве мы явно передавали числа в функцию `STEP`, но мы можем использовать `_`, чтобы доверить Agda вывести значение в нужной позиции с помощью проверки типов.

```agda
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP _ (STEP _ ZERO)
```

##

Мы так же можем использовать неявные параметры во время определения типа:

```agda
data _even : ℕ → Set where
   ZERO : zero even
   STEP : { x : ℕ } → x even → suc (suc x) even    
   -- вместо { x : ℕ } можно использовать ∀ {x}
```

##

Тогда можно переписать наше доказательство:

```agda
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (STEP ZERO)
```

##

Неявные параметры можно передать явно используя фигурные скобки:

```agda
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP {suc (suc zero)} (STEP {zero} ZERO)
```

## Импликация

Импликации ⇒ в Agda соответствует функциональный тип →

##

Пример доказательства, которое можно прочитать как "из существования ℕ следует существование ℕ":

```agda
proof₂ : ℕ → ℕ
proof₂ ν = ν      -- type \nu for ν.
```

## Квантор всеобщности

Мы можем обобщить предыдущий пример на произвольное множество A используя квантор всеообщности:

```agda
proof₂′ : (A : Set) → A → A
proof₂′ _ x = x
```

## Конъюнкция

Конъюнкции соответствует тип пары(тип произведения):

```agda
data _∧_ (P : Set) (Q : Set) : Set where
    pair : P → Q → (P ∧ Q)
```

##

Теперь докажем, что P ∧ Q ⇒ P и  P ∧ Q ⇒ Q

```agda
proof₃ : {P Q : Set} → (P ∧ Q) → P
proof₃  (pair p q) = p

proof₄ : {P Q : Set} → (P ∧ Q) → Q
proof₄  (pair p q) = q
```

## Эквивалентность

Введём эквивалентность как существование импликации в обе стороны:

```agda
_⇔_ : (P : Set) → (Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)
```

Теперь можно доказать пару интересных утверждений:

## Коммутативность конъюнкции

```agda
∧-comm′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm′ (pair p q) = pair q p

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = pair ∧-comm′ ∧-comm′
```

## Ассоциативность конъюнкции

```agda
∧-assoc₁ : { P Q R : Set } → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (pair (pair p q) r) = pair p (pair q r)

∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (pair p (pair q r)) = pair (pair p q) r

∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
∧-assoc = pair ∧-assoc₁ ∧-assoc₂
```

## Дизъюнкция

Дизъюнкции соответствует тип суммы:

```agda
data _∨_ (P Q : Set) : Set where
   Left : P → P ∨ Q
   Right : Q → P ∨ Q
```

## Удаление дизъюнкции

```agda
∨-elim : {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
∨-elim ac bc (Left a) = ac a
∨-elim ac bc (Right b) = bc b
```

## Коммутативность дизъюнкции

```agda
∨-comm′ : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm′ (Left p) = Right p
∨-comm′ (Right q) = Left q

∨-comm : {P Q : Set} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = pair ∨-comm′ ∨-comm′
```

## Отрицание

Определим пустое множество как тип без конструкторов и отрицание как функцию переводящую любое множество в пустое:

```agda
data ⊥ : Set where

¬ : Set → Set -- for ¬ type \neg
¬ A = A → ⊥
```