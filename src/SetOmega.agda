module SetOmega where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


-- equality for Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congωl : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congωl f refl = refl

conglω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
conglω f refl = refl

congωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congωω f refl = refl

-- conglωω : ∀ {a} {A : Set a} {B : Setω} {C : Setω} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ω y₂ → f x₁ y₁ ≡ω f x₂ y₂
-- conglωω f refl refl = refl

transω : ∀ {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω refl refl = refl

symω : ∀ {A : Setω} {x y : A} → x ≡ω y → y ≡ω x
symω refl = refl

substω : ∀ {b}{A : Setω} → (F : (x : A) → Set b) →
  ∀ {x y : A} → x ≡ω y → F x → F y
substω f refl x = x

substlω : ∀ {a b}{A : Set a}{B : Setω} → (F : (x : A) → B → Set b) →
  ∀ {x₁ y₁ : A} {x₂ y₂ : B} → x₁ ≡ y₁ → x₂ ≡ω y₂ → F x₁ x₂ → F y₁ y₂
substlω F refl refl x = x

substωl : ∀ {a}{A : Set a} → (F : (x : A) → Setω) →
  ∀ {x y : A} → x ≡ y → F x → F y
substωl f refl x = x


