module ExprTypeSub where

open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Data.List using (List; []; _∷_)

open import Prelude
open import Type
open import TypeSub as T hiding (_⋯ᵣ_; _⋯ₛ_; wkᵣ; ⦅_⦆ₛ; _[_])
open import TypeSubProp
open import Expr

-- necessary to enforce order preservation
-- can _not_ define a mapping over TypeCtx applying the type renamings/substituions 
-- to all elemens in the context, because of tskip constructor
-- thus this relation is needed to relate Γ₁ and Γ₂ 
data Ren : Δ₁ ⇒ᵣ Δ₂ → TypeCtx Δ₁ → TypeCtx Δ₂ → Set where
  id : Ren idᵣ Γ Γ 
  ↑  : ∀ {ρ} → Ren ρ Γ₁ Γ₂ → Ren ρ (t ∷ Γ₁) ((t T.⋯ᵣ ρ) ∷ Γ₂)
  ↑ₗ : ∀ {ρ} → Ren ρ Γ₁ Γ₂ → Ren (ρ ↑ᵣ _) (l ∷⋆ Γ₁) (l ∷⋆ Γ₂)
  wk : ∀ {ρ} → Ren ρ Γ₁ Γ₂ → Ren (wkᵣ' _ ρ) Γ₁ (l ∷⋆ Γ₂)

_⋯ᵣ_ : Δ₁ ⍮ Γ₁ ⊢ t → {ρ : Δ₁ ⇒ᵣ Δ₂} → Ren ρ Γ₁ Γ₂ → Δ₂ ⍮ Γ₂ ⊢ (t T.⋯ᵣ ρ)
(# n)     ⋯ᵣ ρ = # n
(` x)     ⋯ᵣ ρ = ` (x ⋯ᵣ' ρ)
  where _⋯ᵣ'_ : {t : Δ₁ ⊢ l} → {ρ : Δ₁ ⇒ᵣ Δ₂} → Γ₁ ∍ t → Ren ρ Γ₁ Γ₂ → Γ₂ ∍ (t T.⋯ᵣ ρ)
        x       ⋯ᵣ' id   = subst (_ ∍_) (sym (⋯ᵣ-id _)) x
        here    ⋯ᵣ' ↑ ρ  = here
        there x ⋯ᵣ' ↑ ρ  = there (x ⋯ᵣ' ρ)
        skip x  ⋯ᵣ' ↑ₗ ρ = subst (_ ∍_) (wkᵣ-↑ᵣ _ _) (skip (x ⋯ᵣ' ρ))
        x ⋯ᵣ' wk ρ = subst (_ ∍_) (⋯ᵣᵣ-fusion _ _ _) (skip (x ⋯ᵣ' ρ))
(λx e)    ⋯ᵣ ρ = λx (e ⋯ᵣ ↑ ρ)
(Λ[α∶ l ] e)    ⋯ᵣ ρ = Λ[α∶ l ] (e ⋯ᵣ ↑ₗ ρ)
(e₁ · e₂) ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
_⋯ᵣ_ (_∙_ {t = t} e t') {ρ = ρ} ⊢ρ = subst (_ ⍮ _ ⊢_) (⦅⦆ₛ-↑ᵣ t t' ρ) ((e ⋯ᵣ ⊢ρ) ∙ (t' T.⋯ᵣ ρ))

wkᵣ : Δ ⍮ Γ ⊢ t → (l ∷ Δ) ⍮ (l ∷⋆ Γ) ⊢ (t T.⋯ᵣ T.wkᵣ _) 
wkᵣ e = e ⋯ᵣ wk id

data Sub : Δ₁ ⇒ₛ Δ₂ → TypeCtx Δ₁ → TypeCtx Δ₂ → Set where
  id  : Sub idₛ Γ Γ 
  ↑   : ∀ {σ} → Sub σ Γ₁ Γ₂ → Sub σ (t ∷ Γ₁) ((t T.⋯ₛ σ) ∷ Γ₂)
  ↑ₗ  : ∀ {σ} → Sub σ Γ₁ Γ₂ → Sub (σ ↑ₛ _) (l ∷⋆ Γ₁) (l ∷⋆ Γ₂)
  ext : ∀ {σ} → Sub σ Γ₁ Γ₂ → Sub (extₛ t σ) (l ∷⋆ Γ₁) Γ₂

_⋯ₛ_ : Δ₁ ⍮ Γ₁ ⊢ t → {σ : Δ₁ ⇒ₛ Δ₂} → Sub σ Γ₁ Γ₂ → Δ₂ ⍮ Γ₂ ⊢ (t T.⋯ₛ σ)
(# n)        ⋯ₛ σ = # n
(` x)        ⋯ₛ σ    = ` (x ⋯ₛ' σ)
  where _⋯ₛ'_ : {t : Δ₁ ⊢ l} → {σ : Δ₁ ⇒ₛ Δ₂} → Γ₁ ∍ t → Sub σ Γ₁ Γ₂ → Γ₂ ∍ (t T.⋯ₛ σ)
        x ⋯ₛ' id = subst (_ ∍_) (sym (⋯ₛ-id _)) x
        here           ⋯ₛ' ↑ σ   = here
        there x        ⋯ₛ' ↑ σ   = there (x ⋯ₛ' σ)
        skip {t = t} x ⋯ₛ' ↑ₗ σ  = subst (_ ∍_) (wkᵣ-↑ₛ t _) (skip (x ⋯ₛ' σ))
        skip {t = t} x ⋯ₛ' ext σ = subst (_ ∍_) (sym (wkᵣ-cancels-extₛ t _ _)) (x ⋯ₛ' σ)
(λx e)       ⋯ₛ σ = λx (e ⋯ₛ ↑ σ)
(Λ[α∶ l ] e) ⋯ₛ σ = Λ[α∶ l ] (e ⋯ₛ ↑ₗ σ)
(e₁ · e₂)    ⋯ₛ σ = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
_⋯ₛ_ (_∙_ {t = t} e t') {σ = σ} ⊢ρ = subst (_ ⍮ _ ⊢_) (⦅⦆ₛ-↑ₛ t t' σ) ((e ⋯ₛ ⊢ρ) ∙ (t' T.⋯ₛ σ))

⦅_⦆ₛ : (t : Δ ⊢ l) → Sub T.⦅ t ⦆ₛ (l ∷⋆ Γ) Γ
⦅ t ⦆ₛ = ext id

_[_] : (l ∷ Δ) ⍮ (l ∷⋆ Γ) ⊢ t₁ → (t : Δ ⊢ l) → Δ ⍮ Γ ⊢ (t₁ T.[ t ])
e [ t ] = e ⋯ₛ ⦅ t ⦆ₛ
