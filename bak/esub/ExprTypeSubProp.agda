module ExprTypeSubProp where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude
open import SubstProp
open import Type
open import TypeSub as T hiding (_⋯ᵣ_; _⋯ₛ_; wkᵣ; ⦅_⦆ₛ; Ren; Sub)
open import TypeSubProp as TP hiding (⋯ᵣᵣ-fusion; ⋯ᵣₛ-fusion; ⋯ₛᵣ-fusion; ⋯ₛₛ-fusion)
open import Expr
open import ExprTypeSub
 

⋯ᵣᵣ-fusion : ∀ {t : Δ₁ ⊢ l} (e : Δ₁ ⍮ Γ₁ ⊢ t) {ρ₁' : T.Ren Δ₁ Δ₂} → (ρ₁ : Ren ρ₁' Γ₁ Γ₂) → 
                                              {ρ₂' : T.Ren Δ₂ Δ₃} → (ρ₂ : Ren ρ₂' Γ₂ Γ₃) → 
  (e ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ subst (_ ⍮ _ ⊢_) (sym (TP.⋯ᵣᵣ-fusion _ _ _)) (e ⋯ᵣ (⋯· ρ₁ ρ₂))
⋯ᵣᵣ-fusion (# n)        ρ₁ ρ₂ = refl 
⋯ᵣᵣ-fusion (` x)        ρ₁ ρ₂ = {!   !}
⋯ᵣᵣ-fusion (λx e)       ρ₁ ρ₂ = {!   !}
⋯ᵣᵣ-fusion (Λ[α∶ l ] e) ρ₁ ρ₂ = {!   !}
⋯ᵣᵣ-fusion (e₁ · e₂)    ρ₁ ρ₂ =
  begin 
    ((e₁ ⋯ᵣ ρ₁) ⋯ᵣ ρ₂) · ((e₂ ⋯ᵣ ρ₁) ⋯ᵣ ρ₂)
  ≡⟨ cong₂ _·_ (⋯ᵣᵣ-fusion e₁ ρ₁ ρ₂) (⋯ᵣᵣ-fusion e₂ ρ₁ ρ₂) ⟩
    subst (_ ⍮ _ ⊢_) (sym (TP.⋯ᵣᵣ-fusion _ _ _)) (e₁ ⋯ᵣ (⋯· ρ₁ ρ₂)) · 
    subst (_ ⍮ _ ⊢_) (sym (TP.⋯ᵣᵣ-fusion _ _ _)) (e₂ ⋯ᵣ (⋯· ρ₁ ρ₂))
  ≡⟨ {!   !} ⟩
    subst (_ ⍮ _ ⊢_) (sym (TP.⋯ᵣᵣ-fusion _ _ _)) ((e₁ · e₂) ⋯ᵣ (⋯· ρ₁ ρ₂))
  ∎
⋯ᵣᵣ-fusion (x ∙ t')     ρ₁ ρ₂ = {!   !}