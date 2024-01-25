module Prelude where

open import Level
open import Axiom.Extensionality.Propositional using (Extensionality; ∀-extensionality)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

dep-ext : ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α) 
dep-ext = ∀-extensionality fun-ext _ _

infix 4 _∋_
_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
xs ∋ x = x ∈ xs 

 