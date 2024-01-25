module OmegaEquality where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

cong-ωℓ : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
cong-ωℓ f refl = refl

cong-ωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
cong-ωω f refl = refl

cong-ℓω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
cong-ℓω f refl = refl

cong-ℓωω : ∀ {a} {A : Set a} {B : Setω} {C : Setω} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ω y₂ → f x₁ y₁ ≡ω f x₂ y₂
cong-ℓωω f refl refl = refl

sym-ω : ∀ {A : Setω} {x y : A} → x ≡ω y → y ≡ω x
sym-ω refl = refl


trans-ω : ∀ {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
trans-ω refl refl = refl

module ≡ω-Reasoning {A : Setω} where

  infix  3 _∎ω
  infixr 2 _≡ω⟨⟩_ step-≡ω step-≡ω˘
  infix  1 beginω_

  beginω_ : ∀{x y : A} → x ≡ω y → x ≡ω y
  beginω_ x≡ωy = x≡ωy

  _≡ω⟨⟩_ : ∀ (x {y} : A) → x ≡ω y → x ≡ω y
  _ ≡ω⟨⟩ x≡ωy = x≡ωy

  step-≡ω : ∀ (x {y z} : A) → y ≡ω z → x ≡ω y → x ≡ω z
  step-≡ω _ y≡ωz x≡ωy = trans-ω x≡ωy y≡ωz

  step-≡ω˘ : ∀ (x {y z} : A) → y ≡ω z → y ≡ω x → x ≡ω z
  step-≡ω˘ _ y≡ωz y≡ωx = trans-ω (sym-ω y≡ωx) y≡ωz

  _∎ω : ∀ (x : A) → x ≡ω x
  _∎ω _ = refl

  syntax step-≡ω  x y≡ωz x≡ωy = x ≡ω⟨ x≡ωy ⟩ y≡ωz
  syntax step-≡ω˘ x y≡ωz y≡ωx = x ≡ω˘⟨ y≡ωx ⟩ y≡ωz