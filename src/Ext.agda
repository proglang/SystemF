module Ext where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)

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
