{-# OPTIONS --without-K #-}
module Test where
--
-- open import Nat
-- open import PropositionalEquality
-- open import NatProperties
--
-- f : ℕ → ℕ
-- f x = x * 2
--
-- g : ℕ → ℕ
-- g x = 2 * x
--
-- f=g` : ∀ x → x * 2 ≡ 2 * x
-- f=g` x = *-comm x 2
--
-- f=g`` : ∀ x → f x ≡ g x
-- f=g`` x = *-comm x 2
--
-- -- f=g : f ≡ g
-- -- f=g = f=g`
--
-- uip : {A : Set}{x y : A}{p q : x ≡ y} → p ≡ q
-- uip {p = refl} {refl} = refl

open import Agda.Builtin.Equality
open import Agda.Primitive

uip :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  {p q : x ≡ y}
  → -----------
  p ≡ q
uip {p = refl} {refl} = refl
