module Denotational where

open import Level  using (Setω)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Function using (id)


open import Prelude
open import OmegaEquality
open ≡ω-Reasoning
open import Type
open import TypeSub
open import TypeSubProp
open import Expr

data TypeCtx⋆ : KindCtx → Setω where
  ∅   : TypeCtx⋆ []
  _◁_ : Set l → TypeCtx⋆ Δ → TypeCtx⋆ (l ∷ Δ)

variable
  Γ⋆ Γ⋆₁ Γ⋆₂ Γ⋆₃ Γ⋆' Γ⋆₁' Γ⋆₂' Γ⋆₃' : TypeCtx⋆ Δ

lookup : TypeCtx⋆ Δ → Δ ∋ l → Set l
lookup (⟦t⟧ ◁ Γ⋆) (here refl) = ⟦t⟧
lookup (_ ◁ Γ⋆)   (there α)   = lookup Γ⋆ α

⟦_⟧ₜ : Δ ⊢ l → TypeCtx⋆ Δ → Set l
⟦ `ℕ ⟧ₜ         Γ⋆ = ℕ
⟦ ` x ⟧ₜ        Γ⋆ = lookup Γ⋆ x
⟦ t₁ ⇒ t₂ ⟧ₜ    Γ⋆ = ⟦ t₁ ⟧ₜ Γ⋆ → ⟦ t₂ ⟧ₜ Γ⋆ 
⟦ ∀[α∶ l ] t ⟧ₜ Γ⋆ = (⟦α⟧ : Set l) → ⟦ t ⟧ₜ (⟦α⟧ ◁ Γ⋆) 

Ren⋆ : (ρ : Ren Δ₁ Δ₂) (Γ⋆₁ : TypeCtx⋆ Δ₁) → (Γ⋆₂ : TypeCtx⋆ Δ₂) → Setω
Ren⋆ ρ Γ⋆₁ Γ⋆₂ = ∀ l → (x :  _ ∋ l) → lookup Γ⋆₂ (ρ _ x) ≡ lookup Γ⋆₁ x

idᵣ⋆ : Ren⋆ (idᵣ) Γ⋆ Γ⋆ 
idᵣ⋆ _ _ = refl

wkᵣ⋆ : (⟦t⟧ : Set l) → Ren⋆ (wkᵣ _) Γ⋆ (⟦t⟧ ◁ Γ⋆) 
wkᵣ⋆ _ _ _ = refl

dropᵣ⋆ : {ρ : Ren (l ∷ Δ₁) Δ₂} {⟦α⟧ : Set l} → Ren⋆ ρ (⟦α⟧ ◁ Γ⋆₁) Γ⋆₂ → Ren⋆ (dropᵣ ρ) Γ⋆₁ Γ⋆₂ 
dropᵣ⋆ ρ⋆ _ x = ρ⋆ _ (there x)

_↑ᵣ⋆_ : {ρ : Ren Δ₁ Δ₂} → Ren⋆ ρ Γ⋆₁ Γ⋆₂ → (⟦α⟧ : Set l) → Ren⋆ (ρ ↑ᵣ _) (⟦α⟧ ◁ Γ⋆₁) (⟦α⟧ ◁ Γ⋆₂) 
(ρ⋆ ↑ᵣ⋆ ⟦α⟧) _ (here refl) = refl
(ρ⋆ ↑ᵣ⋆ ⟦α⟧) _ (there x)   = ρ⋆ _ x

⊢Ren⋆ : {ρ : Ren Δ₁ Δ₂} → (ρ⋆ : Ren⋆ ρ Γ⋆₁ Γ⋆₂) → (t : Δ₁ ⊢ l) → ⟦ t ⋯ᵣ ρ ⟧ₜ Γ⋆₂ ≡ ⟦ t ⟧ₜ Γ⋆₁
⊢Ren⋆ ρ⋆ `ℕ           = refl 
⊢Ren⋆ ρ⋆ (` x)        = ρ⋆ _ x
⊢Ren⋆ {Γ⋆₁ = Γ⋆₁} {Γ⋆₂ = Γ⋆₂} ρ⋆ (t₁ ⇒ t₂) 
  rewrite ⊢Ren⋆ {Γ⋆₁ = Γ⋆₁} {Γ⋆₂ = Γ⋆₂} ρ⋆ t₁ | ⊢Ren⋆ {Γ⋆₁ = Γ⋆₁} {Γ⋆₂ = Γ⋆₂} ρ⋆ t₂ = refl
⊢Ren⋆ ρ⋆ (∀[α∶ l ] t) = dep-ext λ where
  ⟦α⟧ → ⊢Ren⋆ (ρ⋆ ↑ᵣ⋆ ⟦α⟧) t

σ→Γ⋆ : Sub Δ₁ Δ₂ → TypeCtx⋆ Δ₂ → TypeCtx⋆ Δ₁ 
σ→Γ⋆ {[]} σ γ⋆ = ∅
σ→Γ⋆ {x ∷ Δ₁} σ γ⋆ = ⟦ σ _ (here refl) ⟧ₜ γ⋆ ◁ σ→Γ⋆ (dropₛ σ) γ⋆

ρ→σ : Ren Δ₁ Δ₂ → Sub Δ₁ Δ₂ 
ρ→σ ρ l x = ` ρ l x

idₛ⋆ : σ→Γ⋆ idₛ Γ⋆ ≡ω Γ⋆
idₛ⋆ {Γ⋆ = Γ⋆} = go idᵣ _ _ (idᵣ⋆ {Γ⋆ = Γ⋆})
  where go : (ρ : Ren Δ₁ Δ₂) (Γ⋆₁ : TypeCtx⋆ Δ₁) (Γ⋆₂ : TypeCtx⋆ Δ₂) → Ren⋆ ρ Γ⋆₁ Γ⋆₂ →
            σ→Γ⋆ (λ l x → ` ρ l x) Γ⋆₂ ≡ω Γ⋆₁
        go ρ ∅ Γ⋆₂ ρ⋆           = refl 
        go ρ (⟦α⟧ ◁ Γ⋆₁) Γ⋆₂ ρ⋆ = beginω 
              (lookup Γ⋆₂ (ρ _ (here refl)) ◁ σ→Γ⋆ (dropₛ (ρ→σ ρ)) Γ⋆₂)
            ≡ω⟨ cong-ωω (λ Γ⋆ → _ ◁ Γ⋆) (go (dropᵣ ρ) Γ⋆₁ Γ⋆₂ (dropᵣ⋆ {Γ⋆₂ = Γ⋆₂} ρ⋆)) ⟩
              (lookup Γ⋆₂ (ρ _ (here refl)) ◁ Γ⋆₁)
            ≡ω⟨ cong-ℓω (_◁ _) (ρ⋆ _ (here refl)) ⟩
              (⟦α⟧ ◁ Γ⋆₁)
          ∎ω

wkₛ⋆ : (σ : Sub Δ₁ Δ₂) (Γ⋆ : TypeCtx⋆ Δ₂) (⟦t⟧ : Set l) → σ→Γ⋆ (wkₛ _ σ) (⟦t⟧ ◁ Γ⋆) ≡ω σ→Γ⋆ σ Γ⋆
wkₛ⋆ {[]} σ Γ⋆ ⟦t⟧ = refl
wkₛ⋆ {l ∷ Δ₁} σ Γ⋆ ⟦t⟧ = beginω 
    (⟦ σ l (here refl) ⋯ᵣ wkᵣ _ ⟧ₜ (⟦t⟧ ◁ Γ⋆) ◁ σ→Γ⋆ _ (⟦t⟧ ◁ Γ⋆))
  ≡ω⟨ cong-ℓω ((_◁ σ→Γ⋆ (dropₛ (wkₛ _ σ)) (⟦t⟧ ◁ Γ⋆))) (⊢Ren⋆ {Γ⋆₁ = Γ⋆} (wkᵣ⋆ {Γ⋆ = Γ⋆} ⟦t⟧) (σ _ (here refl))) ⟩
    (⟦ σ l (here refl) ⟧ₜ Γ⋆ ◁ σ→Γ⋆ (dropₛ (wkₛ _ σ)) (⟦t⟧ ◁ Γ⋆))
  ≡ω⟨ cong-ωω (_ ◁_) (wkₛ⋆ (dropₛ σ) Γ⋆ ⟦t⟧) ⟩
    (⟦ σ l (here refl) ⟧ₜ Γ⋆ ◁ σ→Γ⋆ _ Γ⋆)
  ∎ω

⊢Sub⋆ : {Γ⋆ : TypeCtx⋆ Δ₂} (σ : Sub Δ₁ Δ₂) (t : Δ₁ ⊢ l) → ⟦ t ⋯ₛ σ ⟧ₜ Γ⋆ ≡ ⟦ t ⟧ₜ (σ→Γ⋆ σ Γ⋆)
⊢Sub⋆ σ `ℕ              = refl
⊢Sub⋆ {Γ⋆ = Γ⋆} σ (` x) = go σ x
  where go : {Γ⋆ : TypeCtx⋆ Δ₂} (σ : Sub Δ₁ Δ₂) (x : _ ∋ l) → ⟦ σ _ x ⟧ₜ Γ⋆ ≡ lookup (σ→Γ⋆ σ Γ⋆) x
        go σ (here refl) = refl
        go σ (there x)   = go (dropₛ σ) x
⊢Sub⋆ σ (t₁ ⇒ t₂)       = cong₂ (λ A B → A → B) (⊢Sub⋆ σ t₁) (⊢Sub⋆ σ t₂)
⊢Sub⋆ σ (∀[α∶ l ] t)    = dep-ext λ ⟦α⟧ → begin 
      ⟦ t ⋯ₛ (σ ↑ₛ l) ⟧ₜ (⟦α⟧ ◁ _)
    ≡⟨ ⊢Sub⋆ (σ ↑ₛ l) t ⟩
      ⟦ t ⟧ₜ (σ→Γ⋆ (σ ↑ₛ l) (⟦α⟧ ◁ _))
    ≡⟨  cong-ωℓ (λ Γ⋆ → ⟦ t ⟧ₜ (⟦α⟧ ◁ Γ⋆)) (wkₛ⋆ σ _ ⟦α⟧) ⟩
      ⟦ t ⟧ₜ (⟦α⟧ ◁ σ→Γ⋆ σ _)
    ∎

⊢⦅⦆ₛ⋆ : {Γ⋆ : TypeCtx⋆ Δ} → (t' : Δ ⊢ l) → (t : (l ∷ Δ) ⊢ l') →
  ⟦ t ⋯ₛ ⦅ t' ⦆ₛ ⟧ₜ Γ⋆ ≡ ⟦ t ⟧ₜ (⟦ t' ⟧ₜ Γ⋆ ◁ Γ⋆)
⊢⦅⦆ₛ⋆ t' t = begin 
    ⟦ t ⋯ₛ extₛ t' idₛ ⟧ₜ _
  ≡⟨ ⊢Sub⋆ (extₛ t' idₛ) t ⟩
    ⟦ t ⟧ₜ _
  ≡⟨ cong-ωℓ (λ Γ⋆ → ⟦ t ⟧ₜ (⟦ t' ⟧ₜ _ ◁ Γ⋆)) idₛ⋆ ⟩
    ⟦ t ⟧ₜ (⟦ t' ⟧ₜ _ ◁ _)
  ∎

⊢ₛ·ₛ⋆ : (σ₁ : Sub Δ₁ Δ₂) → (σ₂ : Sub Δ₂ Δ₃) → (Γ⋆ : TypeCtx⋆ Δ₃) → 
  σ→Γ⋆ σ₁ (σ→Γ⋆ σ₂ Γ⋆) ≡ω σ→Γ⋆ (σ₁ ₛ·ₛ σ₂) Γ⋆
⊢ₛ·ₛ⋆ {Δ₁ = []} σ₁ σ₂ Γ⋆ = refl
⊢ₛ·ₛ⋆ {Δ₁ = l ∷ Δ₁} σ₁ σ₂ Γ⋆ = cong-ℓωω _◁_ (sym (⊢Sub⋆ σ₂ (σ₁ _ (here refl)))) (⊢ₛ·ₛ⋆ (dropₛ σ₁) σ₂ Γ⋆)

data Ctx⋆ : TypeCtx Δ → TypeCtx⋆ Δ → Setω where
   ∅    : Ctx⋆ [] ∅
   _◁_  : ⟦ t ⟧ₜ Γ⋆ → Ctx⋆ Γ Γ⋆ → Ctx⋆ (t ∷ Γ) Γ⋆
   _◁⋆_ : (⟦α⟧ : Set l) → Ctx⋆ Γ Γ⋆ → Ctx⋆ (l ∷⋆ Γ) (⟦α⟧ ◁ Γ⋆)

apply : Ctx⋆ Γ Γ⋆ → Γ ∍ t → ⟦ t ⟧ₜ Γ⋆
apply (⟦t⟧ ◁ γ⋆) here      = ⟦t⟧
apply (⟦t⟧ ◁ γ⋆) (there x) = apply γ⋆ x
apply {Γ⋆ = .(⟦α⟧ ◁ Γ⋆)} (_◁⋆_ {Γ⋆ = Γ⋆} ⟦α⟧ γ⋆) (skip {t = t} x) = 
    subst id (sym (⊢Ren⋆ (wkᵣ⋆ {Γ⋆ = Γ⋆} ⟦α⟧) t)) (apply γ⋆ x)

-- Ctx⋆ : TypeCtx Δ → TypeCtx⋆ Δ → Setω
-- Ctx⋆ {Δ = Δ} Γ Γ⋆ = ∀ l (t : Δ ⊢ l) → Γ ∍ t → ⟦ t ⟧ₜ Γ⋆
-- 
-- ext : Ctx⋆ Γ Γ⋆ → ⟦ t ⟧ₜ Γ⋆ → Ctx⋆ (t ∷ Γ) Γ⋆
-- ext γ⋆ t _ _ here = t
-- ext γ⋆ t _ _ (there x) = γ⋆ _ _ x
-- 
-- ext⋆ : {⟦α⟧ : Set l} → Ctx⋆ Γ Γ⋆ → Ctx⋆ (l ∷⋆ Γ) (⟦α⟧ ◁ Γ⋆)
-- ext⋆ {Γ⋆ = .(⟦α⟧ ◁ _)} {⟦α⟧ = ⟦α⟧} γ⋆ _ _ (skip x) = {! subst id (sym (⊢Ren⋆ (wkᵣ⋆ {Γ⋆ = Γ⋆} ⟦α⟧) t)) (γ⋆ _ _ x)  !}

variable
  γ⋆ γ⋆₁ γ⋆₂ γ⋆₃ γ⋆' γ⋆₁' γ⋆₂' γ⋆₃' : Ctx⋆ Γ Γ⋆

⟦_⟧ₑ : Δ ⍮ Γ ⊢ t → Ctx⋆ Γ Γ⋆ → ⟦ t ⟧ₜ Γ⋆
⟦ # n ⟧ₑ        γ⋆ = n 
⟦ ` x ⟧ₑ        γ⋆ = apply γ⋆ x
⟦ λx e ⟧ₑ       γ⋆ = λ ⟦x⟧ → ⟦ e ⟧ₑ (⟦x⟧ ◁ γ⋆)
⟦ Λ[α∶ l ] e ⟧ₑ γ⋆ = λ ⟦α⟧ → ⟦ e ⟧ₑ (⟦α⟧ ◁⋆ γ⋆)
⟦ e₁ · e₂ ⟧ₑ    γ⋆ = ⟦ e₁ ⟧ₑ γ⋆ (⟦ e₂ ⟧ₑ γ⋆) 
⟦_⟧ₑ {Γ⋆ = Γ⋆} (_∙_ {t = t} e t') γ⋆ = subst id (sym (⊢⦅⦆ₛ⋆ t' t)) (⟦ e ⟧ₑ γ⋆ (⟦ t' ⟧ₜ Γ⋆))  