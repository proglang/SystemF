module Smallstep where

open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)

open import Type
open import TypeSub as T
open import Expr 
open import ExprTypeSub as ET
open import ExprSub as E

data Val : Δ₁ ⍮ Γ₁ ⊢ t → Set where
  V-λ : Val (λx e)
  V-Λ : Val (Λ[α∶ l ] e)

data _↪_ : Δ ⍮ Γ ⊢ t → Δ ⍮ Γ ⊢ t → Set where
  β-λ :
    ((λx e₁) · e₂) ↪ (e₁ E.⋯ₛ E.⦅ e₂ ⦆ₛ)
  β-Λ : ∀ {e : (l ∷ Δ) ⍮ (l ∷⋆ Γ) ⊢ t} {t' : Δ ⊢ l} →
    ((Λ[α∶ l ] e) ∙ t') ↪ (e ET.⋯ₛ ET.⦅ t' ⦆ₛ) 
  ξ-·₁ :
    e₁ ↪ e₁' →
    (e₁ · e₂) ↪ (e₁' · e₂)
  ξ-·₂ :
    Val e₁ →
    e₂ ↪ e₂' →
    (e₁ · e₂) ↪ (e₁ · e₂')
  ξ-∙ :
    e ↪ e' →
    (e ∙ t) ↪ (e' ∙ t)

-- progress : ∀ (e : Δ ⍮ Γ ⊢ t) →
--   Val e ⊎ ∃[ e' ] e ↪ e'
-- progress (λx e)                                   = inj₁ V-λ
-- progress (Λ[α∶ l ] e)                             = inj₁ V-Λ
-- progress (e₁ · e₂) with progress e₁ | progress e₂
-- ... | inj₁ V-λ            | inj₁ val-e₂           = inj₂ (_ , β-λ)
-- ... | inj₁ val-e₁         | inj₂ (e₂' , e₂↪e₂')   = inj₂ (_ , ξ-·₂ val-e₁ e₂↪e₂')
-- ... | inj₂ (e₁' , e₁↪e₁') | _                     = inj₂ (_ , ξ-·₁ e₁↪e₁')
-- progress (e ∙ t') with progress e
-- ... | inj₁ (V-Λ {e = e})                          = inj₂ (_ , β-Λ {e = e} {t' = t'})
-- ... | inj₂ (e' , e↪e')                            = inj₂ (_ , ξ-∙ e↪e')
