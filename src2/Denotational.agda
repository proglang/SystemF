module Denotational where

open import Level  using (Setω)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Function using (id)


open import Prelude
open import Type
open import TypeSub
open import Expr

data TypeCtx⋆ : KindCtx → Setω where
  ∅   : TypeCtx⋆ []
  _▷_ : Set l → TypeCtx⋆ Δ → TypeCtx⋆ (l ∷ Δ)

variable
  Γ⋆ Γ⋆₁ Γ⋆₂ Γ⋆₃ Γ⋆' Γ⋆₁' Γ⋆₂' Γ⋆₃' : TypeCtx⋆ Δ

lookup : TypeCtx⋆ Δ → Δ ∋ l → Set l
lookup (⟦t⟧ ▷ Γ⋆) (here refl) = ⟦t⟧
lookup (_ ▷ Γ⋆) (there α) = lookup Γ⋆ α

⟦_⟧ₜ : Δ ⊢ l → TypeCtx⋆ Δ → Set l
⟦ `ℕ ⟧ₜ Γ⋆ = ℕ
⟦ ` x ⟧ₜ Γ⋆ = lookup Γ⋆ x
⟦ t₁ ⇒ t₂ ⟧ₜ Γ⋆ = ⟦ t₁ ⟧ₜ Γ⋆ → ⟦ t₂ ⟧ₜ Γ⋆ 
⟦ ∀[α∶ l ] t ⟧ₜ Γ⋆ = (⟦α⟧ : Set l) → ⟦ t ⟧ₜ (⟦α⟧ ▷ Γ⋆) 

Ren⋆ : (ρ : Ren Δ₁ Δ₂) (Γ⋆₁ : TypeCtx⋆ Δ₁) → (Γ⋆₂ : TypeCtx⋆ Δ₂) → Setω
Ren⋆ ρ Γ⋆₁ Γ⋆₂ = ∀ l → (x :  _ ∋ l) → lookup Γ⋆₂ (ρ _ x) ≡ lookup Γ⋆₁ x

idᵣ⋆ : (⟦α⟧ : Set l) → Ren⋆ (idᵣ) Γ⋆ Γ⋆ 
idᵣ⋆ _ _ _ = refl

wkᵣ⋆ : (⟦α⟧ : Set l) → Ren⋆ (wkᵣ _) Γ⋆ (⟦α⟧ ▷ Γ⋆) 
wkᵣ⋆ _ _ _ = refl

_↑ᵣ⋆_ : {ρ : Ren Δ₁ Δ₂} → Ren⋆ ρ Γ⋆₁ Γ⋆₂ → (⟦α⟧ : Set l) → Ren⋆ (ρ ↑ᵣ _) (⟦α⟧ ▷ Γ⋆₁) (⟦α⟧ ▷ Γ⋆₂) 
(ρ⋆ ↑ᵣ⋆ ⟦α⟧) _ (here refl) = refl
(ρ⋆ ↑ᵣ⋆ ⟦α⟧) _ (there x) = ρ⋆ _ x

⊢Ren⋆ : {ρ : Ren Δ₁ Δ₂} → (ρ⋆ : Ren⋆ ρ Γ⋆₁ Γ⋆₂) → (t : Δ₁ ⊢ l) → ⟦ t ⋯ᵣ ρ ⟧ₜ Γ⋆₂ ≡ ⟦ t ⟧ₜ Γ⋆₁
⊢Ren⋆ ρ⋆ `ℕ = refl 
⊢Ren⋆ ρ⋆ (` x) = ρ⋆ _ x
⊢Ren⋆ ρ⋆ (∀[α∶ l ] t) = dep-ext λ where
  ⟦α⟧ → ⊢Ren⋆ (ρ⋆ ↑ᵣ⋆ ⟦α⟧) t
⊢Ren⋆ {Γ⋆₁ = Γ⋆₁} {Γ⋆₂ = Γ⋆₂} ρ⋆ (t₁ ⇒ t₂) 
  rewrite ⊢Ren⋆ {Γ⋆₁ = Γ⋆₁} {Γ⋆₂ = Γ⋆₂} ρ⋆ t₁ | ⊢Ren⋆ {Γ⋆₁ = Γ⋆₁} {Γ⋆₂ = Γ⋆₂} ρ⋆ t₂ = refl
  
Sub→TypeCtx⋆ : Sub Δ₁ Δ₂ → TypeCtx⋆ Δ₂ → TypeCtx⋆ Δ₁ 
Sub→TypeCtx⋆ {[]} σ γ⋆ = ∅
Sub→TypeCtx⋆ {x ∷ Δ₁} σ γ⋆ = ⟦ σ _ (here refl) ⟧ₜ γ⋆ ▷ Sub→TypeCtx⋆ (dropₛ σ) γ⋆

data Ctx⋆ : TypeCtx Δ → TypeCtx⋆ Δ → Setω where
   ∅    : Ctx⋆ [] ∅
   _▷_  : ⟦ t ⟧ₜ Γ⋆ → Ctx⋆ Γ Γ⋆ → Ctx⋆ (t ∷ Γ) Γ⋆
   _▷⋆_ : (⟦α⟧ : Set l) → Ctx⋆ Γ Γ⋆ → Ctx⋆ (l ∷⋆ Γ) (⟦α⟧ ▷ Γ⋆)

apply : Ctx⋆ Γ Γ⋆ → Γ ∍ t → ⟦ t ⟧ₜ Γ⋆
apply (⟦t⟧ ▷ γ⋆) here = ⟦t⟧
apply (⟦t⟧ ▷ γ⋆) (there x) = apply γ⋆ x
apply {Γ⋆ = .(⟦α⟧ ▷ Γ⋆)} (_▷⋆_ {Γ⋆ = Γ⋆} ⟦α⟧ γ⋆) (skip {t = t} x) = 
    subst id (sym (⊢Ren⋆ (wkᵣ⋆ {Γ⋆ = Γ⋆} ⟦α⟧) t)) (apply γ⋆ x)

    
variable
  γ⋆ γ⋆₁ γ⋆₂ γ⋆₃ γ⋆' γ⋆₁' γ⋆₂' γ⋆₃' : Ctx⋆ Γ Γ⋆

⟦_⟧ₑ : Δ ⍮ Γ ⊢ t → Ctx⋆ Γ Γ⋆ → ⟦ t ⟧ₜ Γ⋆
⟦ # n ⟧ₑ γ⋆ = n 
⟦ ` x ⟧ₑ γ⋆ = apply γ⋆ x
⟦ λx e ⟧ₑ γ⋆ = λ ⟦x⟧ → ⟦ e ⟧ₑ (⟦x⟧ ▷ γ⋆)
⟦ Λ[α∶ l ] e ⟧ₑ γ⋆ = λ ⟦α⟧ → ⟦ e ⟧ₑ (⟦α⟧ ▷⋆ γ⋆)
⟦ e₁ · e₂ ⟧ₑ γ⋆ = ⟦ e₁ ⟧ₑ γ⋆ (⟦ e₂ ⟧ₑ γ⋆)
⟦ e ∙ t' ⟧ₑ γ⋆ = {!   !}