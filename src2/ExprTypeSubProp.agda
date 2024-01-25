module ExprTypeSubProp where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude
open import SubstProp
open import Type
open import TypeSub hiding (_⋯ᵣ_; _⋯ₛ_; wkᵣ; ⦅_⦆ₛ)
open import TypeSubProp as T hiding (⋯ᵣᵣ-fusion; ⋯ᵣₛ-fusion; ⋯ₛᵣ-fusion; ⋯ₛₛ-fusion)
open import Expr
open import ExprTypeSub
 

⋯ᵣᵣ-fusion : ∀ {t : Δ₁ ⊢ l} (e : Δ₁ ⍮ Γ₁ ⊢ t) {ρ₁ : Δ₁ ⇒ᵣ Δ₂} → (r₁ : Ren ρ₁ Γ₁ Γ₂) → 
                                              {ρ₂ : Δ₂ ⇒ᵣ Δ₃} → (r₂ : Ren ρ₂ Γ₂ Γ₃) → 
  (e ⋯ᵣ r₁) ⋯ᵣ r₂ ≡ subst (_ ⍮ _ ⊢_) (sym (T.⋯ᵣᵣ-fusion _ _ _)) (e ⋯ᵣ (⋯· r₁ r₂))
⋯ᵣᵣ-fusion (# n)        r₁ r₂ = refl 
⋯ᵣᵣ-fusion (` x)        r₁ r₂ = {!   !}
⋯ᵣᵣ-fusion (λx e)       r₁ r₂ = {!   !}
⋯ᵣᵣ-fusion (Λ[α∶ l ] e) r₁ r₂ = {!   !}
⋯ᵣᵣ-fusion (e₁ · e₂)    r₁ r₂ =
  begin 
    ((e₁ ⋯ᵣ r₁) ⋯ᵣ r₂) · ((e₂ ⋯ᵣ r₁) ⋯ᵣ r₂)
  ≡⟨ cong₂ _·_ (⋯ᵣᵣ-fusion e₁ r₁ r₂) (⋯ᵣᵣ-fusion e₂ r₁ r₂) ⟩
    subst (_ ⍮ _ ⊢_) (sym (T.⋯ᵣᵣ-fusion _ _ _)) (e₁ ⋯ᵣ (⋯· r₁ r₂)) · 
    subst (_ ⍮ _ ⊢_) (sym (T.⋯ᵣᵣ-fusion _ _ _)) (e₂ ⋯ᵣ (⋯· r₁ r₂))
  ≡⟨ {!   !} ⟩
    subst (_ ⍮ _ ⊢_) (sym (T.⋯ᵣᵣ-fusion _ _ _)) ((e₁ · e₂) ⋯ᵣ (⋯· r₁ r₂))
  ∎
⋯ᵣᵣ-fusion (x ∙ t')     r₁ r₂ = {!   !}