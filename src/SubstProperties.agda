open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

module SubstProperties where

dist-subst-app :
  ∀ {ℓ₁ ℓ₂}
    {A A' : Set ℓ₁} {B B' : Set ℓ₂}
  → (f : A → B)
  → (A≡A' : A ≡ A')
  → (A→B≡A'→B' : (A → B) ≡ (A' → B'))
  → (B≡B' : B ≡ B')
  → (x : A) 
  → subst id A→B≡A'→B' f (subst id A≡A' x) ≡ subst id B≡B' (f x)
dist-subst-app _ refl refl refl _ = refl