module ExprTypeSub where

open import Prelude
open import Type
open import TypeSub as T hiding (_⋯ᵣ_; _⋯ₛ_)
open import Expr

data Ren : Δ₁ ⇒ᵣ Δ₂ → TypeCtx Δ₁ → TypeCtx Δ₂ → Set where
  id : Ren idᵣ Γ Γ 
  ↑  : ∀ {ρ} → Ren ρ Γ₁ Γ₂ → Ren ρ (t ∷ Γ₁) ((t T.⋯ᵣ ρ) ∷ Γ₂)
  ↑ₗ : ∀ {ρ} → Ren ρ Γ₁ Γ₂ → Ren (ρ ↑ᵣ _) (l ∷⋆ Γ₁) (l ∷⋆ Γ₂)
  wk : ∀ {ρ} → Ren ρ Γ₁ Γ₂ → Ren (wkᵣ _ ρ) Γ₁ (l ∷⋆ Γ₂)

_⋯ᵣ_ : Δ₁ ⍮ Γ ⊢ t → {ρ : Δ₁ ⇒ᵣ Δ₂} → Ren ρ Γ₁ Γ₂ → Δ₂ ⍮ Γ₂ ⊢ (t T.⋯ᵣ ρ)
(` x)     ⋯ᵣ ρ = {!   !}
(λx e)    ⋯ᵣ ρ = {!   !}
(Λα e)    ⋯ᵣ ρ = {!   !}
-- Λα subst (_ ⍮_⊢ _) eq (e ⋯ᵣ (ρ ↑ᵣ _)) where
--   eq = begin
--          (Γ ⋯ᵣ* wkᵣ k) ⋯ᵣ* (ρ ↑ᵣ k)
--        ≡⟨ sym (wkᵣ-↑ᵣ-* Γ ρ) ⟩
--          (Γ ⋯ᵣ* ρ) ⋯ᵣ* wkᵣ k
--        ∎
(e₁ · e₂) ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
_⋯ᵣ_ {Δ₁ = Δ₁} {Γ = Γ} {Δ₂ = Δ₂} (_∙_ {t₂ = t₂'} e₁ t₂) ρ = {!   !}
-- subst (Δ₂ ⍮ Γ ⋯ᵣ* ρ ⊢_)
--       (⦅⦆ₛ-↑ᵣ t₂' t₂ ρ)
--       ((e₁ ⋯ᵣ ρ) ∙ (t₂ Ty.⋯ᵣ ρ))