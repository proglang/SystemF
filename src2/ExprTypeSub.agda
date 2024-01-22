module ExprTypeSub where

open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Data.List using (List; []; _∷_)

open import Prelude
open import Type
open import TypeSub as T hiding (_⋯ᵣ_; _⋯ₛ_; wkᵣ; ⦅_⦆ₛ)
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
  ↑   : ∀ {ρ} → Sub ρ Γ₁ Γ₂ → Sub ρ (t ∷ Γ₁) ((t T.⋯ₛ ρ) ∷ Γ₂)
  ↑ₗ  : ∀ {ρ} → Sub ρ Γ₁ Γ₂ → Sub (ρ ↑ₛ _) (l ∷⋆ Γ₁) (l ∷⋆ Γ₂)
  ext : ∀ {ρ} → Sub ρ Γ₁ Γ₂ → Sub (extₛ t ρ) (l ∷⋆ Γ₁) Γ₂

_⋯ₛ_ : Δ₁ ⍮ Γ₁ ⊢ t → {ρ : Δ₁ ⇒ₛ Δ₂} → Sub ρ Γ₁ Γ₂ → Δ₂ ⍮ Γ₂ ⊢ (t T.⋯ₛ ρ)
(` x)     ⋯ₛ ρ    = ` (x ⋯ₛ' ρ)
  where _⋯ₛ'_ : {t : Δ₁ ⊢ l} → {ρ : Δ₁ ⇒ₛ Δ₂} → Γ₁ ∍ t → Sub ρ Γ₁ Γ₂ → Γ₂ ∍ (t T.⋯ₛ ρ)
        x ⋯ₛ' id = subst (_ ∍_) (sym (⋯ₛ-id _)) x
        here           ⋯ₛ' ↑ ρ   = here
        there x        ⋯ₛ' ↑ ρ   = there (x ⋯ₛ' ρ)
        skip {t = t} x ⋯ₛ' ↑ₗ ρ  = subst (_ ∍_) (wkᵣ-↑ₛ t _) (skip (x ⋯ₛ' ρ))
        skip {t = t} x ⋯ₛ' ext ρ = subst (_ ∍_) (sym (wkᵣ-cancels-extₛ t _ _)) (x ⋯ₛ' ρ)
(λx e)    ⋯ₛ ρ = λx (e ⋯ₛ ↑ ρ)
(Λ[α∶ l ] e) ⋯ₛ ρ = Λ[α∶ l ] (e ⋯ₛ ↑ₗ ρ)
(e₁ · e₂) ⋯ₛ ρ    = (e₁ ⋯ₛ ρ) · (e₂ ⋯ₛ ρ)
_⋯ₛ_ (_∙_ {t = t} e t') {ρ = ρ} ⊢ρ = subst (_ ⍮ _ ⊢_) (⦅⦆ₛ-↑ₛ t t' ρ) ((e ⋯ₛ ⊢ρ) ∙ (t' T.⋯ₛ ρ))

⦅_⦆ₛ : (t : Δ ⊢ l) → Sub T.⦅ t ⦆ₛ (l ∷⋆ Γ) Γ
⦅ t ⦆ₛ = ext id

