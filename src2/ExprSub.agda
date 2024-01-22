module ExprSub where

open import Prelude
open import Type
open import Expr
open import ExprTypeSub as ET hiding (_⋯ᵣ_; _⋯ₛ_; wkᵣ; ⦅_⦆ₛ)

_⇒ᵣ_ : TypeCtx Δ → TypeCtx Δ → Set
Γ₁ ⇒ᵣ Γ₂ = ∀ l (t : _ ⊢ l) → Γ₁ ∍ t → Γ₂ ∍ t

_⇒ₛ_ : TypeCtx Δ → TypeCtx Δ → Set
Γ₁ ⇒ₛ Γ₂ = ∀ l (t : _ ⊢ l) → Γ₁ ∍ t → _ ⍮ Γ₂ ⊢ t

_↑ᵣ_ : Γ₁ ⇒ᵣ Γ₂ → ∀ (t : _ ⊢ l) → (t ∷ Γ₁) ⇒ᵣ (t ∷ Γ₂)
(ρ ↑ᵣ t) _ _ here      = here 
(ρ ↑ᵣ t) _ _ (there x) = there (ρ _ _ x)

_↑ᵣₗ_ : Γ₁ ⇒ᵣ Γ₂ → ∀ l → (l ∷⋆ Γ₁) ⇒ᵣ (l ∷⋆ Γ₂)
(ρ ↑ᵣₗ l) _ _ (skip x) = skip (ρ _ _ x)

_⋯ᵣ_ : Δ ⍮ Γ₁ ⊢ t → Γ₁ ⇒ᵣ Γ₂ → Δ ⍮ Γ₂ ⊢ t
(` x)        ⋯ᵣ ρ = ` ρ _ _ x
(λx e)       ⋯ᵣ ρ = λx (e ⋯ᵣ (ρ ↑ᵣ _))
(Λ[α∶ l ] e) ⋯ᵣ ρ = Λ[α∶ l ] (e ⋯ᵣ (ρ ↑ᵣₗ _))
(e₁ · e₂)    ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
(e₁ ∙ t₂)    ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) ∙ t₂

wkᵣ : ∀ {l} (t : _ ⊢ l) → Γ ⇒ᵣ (t ∷ Γ)
wkᵣ t _ _ x = there x

_↑ₛ_ : Γ₁ ⇒ₛ Γ₂ → ∀ (t : _ ⊢ l) → (t ∷ Γ₁) ⇒ₛ (t ∷ Γ₂)
(ρ ↑ₛ t) _ _ here    = ` here
(ρ ↑ₛ t) _ _ (there x) = ρ _ _ x ⋯ᵣ wkᵣ _

_↑ₛₗ_ : Γ₁ ⇒ₛ Γ₂ → ∀ l → (l ∷⋆ Γ₁) ⇒ₛ (l ∷⋆ Γ₂)
(ρ ↑ₛₗ l) _ _ (skip x) = ET.wkᵣ (ρ _ _ x)

_⋯ₛ_ : Δ ⍮ Γ₁ ⊢ t → Γ₁ ⇒ₛ Γ₂ → Δ ⍮ Γ₂ ⊢ t
(` x)        ⋯ₛ ρ = ρ _ _ x
(λx e)       ⋯ₛ ρ = λx (e ⋯ₛ (ρ ↑ₛ _))
(Λ[α∶ l ] e) ⋯ₛ ρ = Λ[α∶ l ] (e ⋯ₛ (ρ ↑ₛₗ _))
(e₁ · e₂)    ⋯ₛ ρ = (e₁ ⋯ₛ ρ) · (e₂ ⋯ₛ ρ)
(e₁ ∙ t₂)    ⋯ₛ ρ = (e₁ ⋯ₛ ρ) ∙ t₂

⦅_⦆ₛ : Δ ⍮ Γ ⊢ t → (t ∷ Γ) ⇒ₛ Γ
⦅ t ⦆ₛ _ _ here    = t
⦅ t ⦆ₛ _ _ (there x) = ` x