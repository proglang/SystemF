module Ext where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import SetOmega

----------------------------------------------------------------------

postulate
  fun-ext : ∀{a b} → Extensionality a b

fun-ext₂ : ∀ {l₁}{l₂}{l₃} {A₁ : Set l₁} {A₂ : A₁ → Set l₂} {B : (x : A₁) → A₂ x → Set l₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

dep-ext : ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α) 
dep-ext = ∀-extensionality fun-ext _ _

postulate 
  fun-ext₂′ :  ∀ {l₁}{l₂}{l₃}{l₄} {A₁ : Set l₁} {A₂ : A₁ → Set l₂} {A₃ : (x : A₁) → A₂ x → Set l₃}{B : (x : A₁) → (y : A₂ x) → A₃ x y → Set l₄}
             {f g : (x : A₁) → {y : A₂ x} → (z : A₃ x y) → B x y z} →
    (∀ (x : A₁) {y : A₂ x} (z : A₃ x y) → f x {y} z ≡ g x {y} z) →
    f ≡ g

postulate 
  fun-ext₂″ :  ∀ {l₁}{l₂}{l₃}{l₄} {A₁ : Set l₁} {A₂ : A₁ → Set l₂} {A₃ : (x : A₁) → A₂ x → Set l₃}{B : (x : A₁) → (y : A₂ x) → A₃ x y → Set l₄}
             {f g : (x : A₁) → {y : A₂ x} → (z : A₃ x y) → B x y z} →
    (∀ (x : A₁) (y : A₂ x) (z : A₃ x y) → f x {y} z ≡ g x {y} z) →
    f ≡ g


postulate
  fun-extω : {B : (l : Level) → Set l} {f g : (x : Level) → B x} →
    (∀ x → f x ≡ g x) → f ≡ω g

postulate
  fun-ext-llω-ω :
    -- ∀{a} {A : Set a}
    ∀ {b} {B : Level → Set b} {c} {C : (x : Level) (y : B x) → Set c}
      {D : (x : Level) (y : B x) (z : C x y) → Set x}
    → {f g : ∀ (x : Level) (y : B x) (z : C x y) → D x y z}
    → (∀ x y z → f x y z ≡ g x y z)
    → f ≡ω g

