module ExprSubProp where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude
open import Type
open import Expr
open import ExprSub

_ᵣ·ᵣ_ : Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
(ρ₁ ᵣ·ᵣ ρ₂) _ _ x = ρ₂ _ _ (ρ₁ _ _ x)

↑ᵣ-dist-ᵣ·ᵣ : ∀ (ρ₁ : Ren Γ₁ Γ₂) (ρ₂ : Ren Γ₂ Γ₃) →
  (ρ₁ ↑ᵣ t) ᵣ·ᵣ (ρ₂ ↑ᵣ t) ≡ (ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣ t
↑ᵣ-dist-ᵣ·ᵣ ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ _ → fun-ext λ where
  here → refl 
  (there x) → refl

↑ᵣₗ-dist-ᵣ·ᵣ : ∀ (ρ₁ : Ren Γ₁ Γ₂) (ρ₂ : Ren Γ₂ Γ₃) →
  (ρ₁ ↑ᵣₗ l) ᵣ·ᵣ (ρ₂ ↑ᵣₗ l) ≡ (ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣₗ l
↑ᵣₗ-dist-ᵣ·ᵣ ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ _ → fun-ext λ where
  (skip x) → refl

⋯ᵣᵣ-fusion : ∀ (e : Δ ⍮ Γ₁ ⊢ t) (ρ₁ : Ren Γ₁ Γ₂) (ρ₂ : Ren Γ₂ Γ₃) →
  (e ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ e ⋯ᵣ (ρ₁ ᵣ·ᵣ ρ₂)
⋯ᵣᵣ-fusion (# n)        ρ₁ ρ₂ = refl 
⋯ᵣᵣ-fusion (` x)        ρ₁ ρ₂ = refl
⋯ᵣᵣ-fusion (λx e)       ρ₁ ρ₂ = cong λx_ (
  begin
    (e ⋯ᵣ (ρ₁ ↑ᵣ _)) ⋯ᵣ (ρ₂ ↑ᵣ _)
  ≡⟨ ⋯ᵣᵣ-fusion e (ρ₁ ↑ᵣ _) (ρ₂ ↑ᵣ _) ⟩
    e ⋯ᵣ ((ρ₁ ↑ᵣ _) ᵣ·ᵣ (ρ₂ ↑ᵣ _))
  ≡⟨ cong (e ⋯ᵣ_) (↑ᵣ-dist-ᵣ·ᵣ ρ₁ ρ₂) ⟩
    e ⋯ᵣ ((ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣ _)
  ∎)
⋯ᵣᵣ-fusion (Λ[α∶ l ] e) ρ₁ ρ₂ = cong Λ[α∶ l ]_ (
  begin
    (e ⋯ᵣ (ρ₁ ↑ᵣₗ _)) ⋯ᵣ (ρ₂ ↑ᵣₗ _)
  ≡⟨ ⋯ᵣᵣ-fusion e (ρ₁ ↑ᵣₗ _) (ρ₂ ↑ᵣₗ _) ⟩
    e ⋯ᵣ ((ρ₁ ↑ᵣₗ _) ᵣ·ᵣ (ρ₂ ↑ᵣₗ _))
  ≡⟨ cong (e ⋯ᵣ_) (↑ᵣₗ-dist-ᵣ·ᵣ ρ₁ ρ₂) ⟩
    e ⋯ᵣ ((ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣₗ _)
  ∎)
⋯ᵣᵣ-fusion (e₁ · e₂)    ρ₁ ρ₂ = cong₂ _·_ (⋯ᵣᵣ-fusion e₁ ρ₁ ρ₂) (⋯ᵣᵣ-fusion e₂ ρ₁ ρ₂)
⋯ᵣᵣ-fusion (e ∙ t')     ρ₁ ρ₂ = cong (_∙ t') (⋯ᵣᵣ-fusion e ρ₁ ρ₂)