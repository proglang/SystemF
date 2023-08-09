open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

module SubstProperties where

subst-irrelevant : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq eq' : a₁ ≡ a₂)
    (x : F a₁) 
  → subst F eq x ≡ subst F eq' x
subst-irrelevant refl refl x = refl

elim-subst :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ a₄ : A}
  → (F : A → Set ℓ₁)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F a₂≡a₁ (subst F a₁≡a₂ x) ≡ x
elim-subst _ refl refl _ = refl

elim-subst₃ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ a₄ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (a₃≡a₁ : a₃ ≡ a₁)
  → (a₂≡a₃ : a₂ ≡ a₃)
  → (x : F a₂)
  → subst F a₁≡a₂ (subst F a₃≡a₁ (subst F a₂≡a₃ x)) ≡ x
elim-subst₃ _ refl refl refl _ = refl

dist-subst :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A′ ≡ A)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A′) 
  → subst id B≡B′ (f (subst id A≡A′ x)) ≡ subst id A→B≡A′→B′ f x
dist-subst _ refl refl refl _ = refl

dist-subst′ :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A ≡ A′)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A) 
  → subst id A→B≡A′→B′ f (subst id A≡A′ x) ≡ subst id B≡B′ (f x)
dist-subst′ _ refl refl refl _ = refl
