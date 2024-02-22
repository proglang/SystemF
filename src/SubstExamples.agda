-- This file is only used to generate examples for the paper, and is
-- not part of the actual formalization.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

--! SubstExamples >

--! Def
subst : ∀ {ℓ ℓ′} {A : Set ℓ} {x y : A} (P : A → Set ℓ′) → x ≡ y → P x → P y
subst P refl Px = Px

open import Types
open import TypeSubstitution hiding (_∘ₛₛ_)
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution hiding (Eidₛ; ESub)

--! ESubDef
ESub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ESub {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ* Γ₁ Γ₂ = ∀ l (T : Type Δ₁ l) → inn T Γ₁ → Expr Δ₂ Γ₂ (Tsub σ* T)

--! EidDef
Eidₛ : ESub Tidₛ Γ Γ
Eidₛ _ T x = subst (Expr _ _) (sym (TidₛT≡T T)) (` x)

--! EidNeutral
Eidₛe≡e : ∀ (e : Expr Δ Γ T) → Esub Tidₛ Eidₛ e ≡ subst (Expr Δ Γ) (sym (TidₛT≡T _)) e
Eidₛe≡e {Δ = Δ} {Γ = Γ} (`suc e) =
  Esub Tidₛ Eidₛ (`suc e)                       ≡⟨ refl ⟩
  `suc (Esub Tidₛ Eidₛ e)                       ≡⟨ cong `suc (Eidₛe≡e e) ⟩
  `suc (subst (Expr Δ Γ) (sym (TidₛT≡T `ℕ)) e)  ≡⟨ {!!} ⟩
  subst (Expr Δ Γ) (sym (TidₛT≡T `ℕ)) (`suc e)  ∎

Eidₛe≡e = {!!}

-- _∘ₛₛ_ : TSub Δ₂ Δ₃ → TSub Δ₁ Δ₂ → TSub Δ₁ Δ₃
-- (σ₂ ∘ₛₛ σ₁) _ x = Tsub σ₂ (σ₁ _ x)

-- _∘′ₛₛ_ : ∀ {Δ₁ Δ₂ Δ₃} {σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
--   → ESub σ₂* Γ₂ Γ₃ → ESub σ₁* Γ₁ Γ₂ → ESub (σ₂* ∘ₛₛ σ₁*) Γ₁ Γ₃
-- _∘′ₛₛ_ {Δ₃ = Δ₃} {σ₁* = σ₁*} {σ₂* = σ₂*} {Γ₃ = Γ₃} σ₂ σ₁ l T x =
--   subst (Expr Δ₃ Γ₃) (assoc-sub-sub T  σ₁* σ₂*) (Esub _ σ₂ (σ₁ _ _ x))

-- Eassoc-sub-sub : 
--   ∀ {σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃}
--     {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
--     {T : Type Δ₁ l}
--     (e : Expr Δ₁ Γ₁ T)
--     (σ₁ : ESub σ₁* Γ₁ Γ₂) (σ₂ : ESub σ₂* Γ₂ Γ₃) →
--   let sub = subst (Expr Δ₃ Γ₃) (assoc-sub-sub T σ₁* σ₂*) in
--   sub (Esub σ₂* σ₂ (Esub σ₁* σ₁ e)) ≡ Esub (σ₂* ∘ₛₛ σ₁*) (σ₂ ∘′ₛₛ σ₁) e
-- Eassoc-sub-sub {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} e σ ρ =
--   {!!}
