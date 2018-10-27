{-# OPTIONS --without-K #-}
module ex1 {A : Set} where

open import PropositionalEquality {A}

_∘_ : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∘ q = q

J : (P : (x y : A) → x ≡ y → Set) → ((x : A) → P x x refl) → (x y : A) (x≡y : x ≡ y) → P x y x≡y
J P p x .x refl = p x

reflRight : {x y : A} → (p : x ≡ y) → (p ∘ refl) ≡ p
reflRight refl = refl

reflLeft : {x y : A} → (p : x ≡ y) → (refl ∘ p) ≡ p
reflLeft refl = refl

i : (x : A) → x ≡ x
i x = refl
