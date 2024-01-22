module Denotational where

open import Level  using (Setω)
open import Data.List using (List; []; _∷_)

open import Prelude
open import Type hiding (_∷⋆_)
open import Expr

data TypeCtx⋆ : KindCtx → Setω where
  []⋆  : TypeCtx⋆ []
  _∷⋆_ : Set l → TypeCtx⋆ Δ → TypeCtx⋆ (l ∷ Δ)

lookup : TypeCtx⋆ Δ → Δ ∋ l → Set l
lookup (⟦t⟧ ∷⋆ Γ⋆) zero = ⟦t⟧
lookup (_ ∷⋆ Γ⋆) (suc α) = lookup Γ⋆ α

⟦_⟧ₜ : Δ ⊢ l → TypeCtx⋆ Δ → Set l
⟦ ` x ⟧ₜ Γ⋆ = lookup Γ⋆ x
⟦ t₁ ⇒ t₂ ⟧ₜ Γ⋆ = ⟦ t₁ ⟧ₜ Γ⋆ → ⟦ t₂ ⟧ₜ Γ⋆ 
⟦ ∀[α∶ l ] t ⟧ₜ Γ⋆ = (⟦α⟧ : Set l) → ⟦ t ⟧ₜ (⟦α⟧ ∷⋆ Γ⋆) 