module ExprSub where

open import Prelude
open import Type
open import Expr
open import ExprTypeSub as ET hiding (_⋯ᵣ_; _⋯ₛ_; wkᵣ; ⦅_⦆ₛ; _[_])

_⇒ᵣ_ : TypeCtx Δ → TypeCtx Δ → Set
Γ₁ ⇒ᵣ Γ₂ = ∀ l (t : _ ⊢ l) → Γ₁ ∍ t → Γ₂ ∍ t

_↑ᵣ_ : Γ₁ ⇒ᵣ Γ₂ → ∀ (t : _ ⊢ l) → (t ∷ Γ₁) ⇒ᵣ (t ∷ Γ₂)
(ρ ↑ᵣ t) _ _ here      = here 
(ρ ↑ᵣ t) _ _ (there x) = there (ρ _ _ x)

_↑ᵣₗ_ : Γ₁ ⇒ᵣ Γ₂ → ∀ l → (l ∷⋆ Γ₁) ⇒ᵣ (l ∷⋆ Γ₂)
(ρ ↑ᵣₗ l) _ _ (skip x) = skip (ρ _ _ x)

_⋯ᵣ_ : Δ ⍮ Γ₁ ⊢ t → Γ₁ ⇒ᵣ Γ₂ → Δ ⍮ Γ₂ ⊢ t
(# n)        ⋯ᵣ ρ = # n 
(` x)        ⋯ᵣ ρ = ` ρ _ _ x
(λx e)       ⋯ᵣ ρ = λx (e ⋯ᵣ (ρ ↑ᵣ _))
(Λ[α∶ l ] e) ⋯ᵣ ρ = Λ[α∶ l ] (e ⋯ᵣ (ρ ↑ᵣₗ _))
(e₁ · e₂)    ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
(e₁ ∙ t₂)    ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) ∙ t₂

wkᵣ : ∀ {l} (t : _ ⊢ l) → Γ ⇒ᵣ (t ∷ Γ)
wkᵣ t _ _ x = there x

_⇒ₛ_ : TypeCtx Δ → TypeCtx Δ → Set
Γ₁ ⇒ₛ Γ₂ = ∀ l (t : _ ⊢ l) → Γ₁ ∍ t → _ ⍮ Γ₂ ⊢ t

_↑ₛ_ : Γ₁ ⇒ₛ Γ₂ → ∀ (t : _ ⊢ l) → (t ∷ Γ₁) ⇒ₛ (t ∷ Γ₂)
(σ ↑ₛ t) _ _ here    = ` here
(σ ↑ₛ t) _ _ (there x) = σ _ _ x ⋯ᵣ wkᵣ _

_↑ₛₗ_ : Γ₁ ⇒ₛ Γ₂ → ∀ l → (l ∷⋆ Γ₁) ⇒ₛ (l ∷⋆ Γ₂)
(σ ↑ₛₗ l) _ _ (skip x) = ET.wkᵣ (σ _ _ x)

_⋯ₛ_ : Δ ⍮ Γ₁ ⊢ t → Γ₁ ⇒ₛ Γ₂ → Δ ⍮ Γ₂ ⊢ t
(# n)        ⋯ₛ σ = # n
(` x)        ⋯ₛ σ = σ _ _ x
(λx e)       ⋯ₛ σ = λx (e ⋯ₛ (σ ↑ₛ _))
(Λ[α∶ l ] e) ⋯ₛ σ = Λ[α∶ l ] (e ⋯ₛ (σ ↑ₛₗ _))
(e₁ · e₂)    ⋯ₛ σ = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
(e₁ ∙ t₂)    ⋯ₛ σ = (e₁ ⋯ₛ σ) ∙ t₂

⦅_⦆ₛ : Δ ⍮ Γ ⊢ t → (t ∷ Γ) ⇒ₛ Γ
⦅ e ⦆ₛ _ _ here    = e
⦅ e ⦆ₛ _ _ (there x) = ` x

_[_] : Δ ⍮ (t₁ ∷ Γ) ⊢ t₂ →  Δ ⍮ Γ ⊢ t₁ → Δ ⍮ Γ ⊢ t₂
e [ e′ ] = e ⋯ₛ ⦅ e′ ⦆ₛ
