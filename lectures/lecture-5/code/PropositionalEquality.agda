module PropositionalEquality {A : Set} where

infix 4 _≡_

data _≡_ {A : Set l} : A → A → Set l where
  refl : { x : A } → x ≡ x

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infix  3 _∎
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl
