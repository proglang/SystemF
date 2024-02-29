-- This file reexports all the individual fusion lemmas for expression substitutions.

module StratF.ExprSubstFusion where

open import StratF.ExprSubstFusion.RenRen  public
open import StratF.ExprSubstFusion.SubRen  public
open import StratF.ExprSubstFusion.SwapRen public
open import StratF.ExprSubstFusion.RenSub  public
open import StratF.ExprSubstFusion.SwapSub public
open import StratF.ExprSubstFusion.SubSub  public

-- TODO: The following lemmas are only required for backwards-compatibility with Homogeneous Equality

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.Util.HeterogeneousEqualityLemmas

--! EF >

--! FusionRenRen
fusion-Eren-Eren : 
    {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → (e : Expr Δ₁ Γ₁ T)
  → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃)
  → let sub = subst (Expr Δ₃ Γ₃) (fusion-Tren-Tren T ρ* σ*) in
    sub (Eren σ* σ (Eren ρ* ρ e)) ≡ Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e

fusion-Eren-Eren {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} e ρ σ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tren-Tren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Eren σ* σ (Eren ρ* ρ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Eren σ* σ (Eren ρ* ρ e)
    R.≅⟨ fusion-Eren-Eren' e ρ σ ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e
    R.∎
  )

--! FusionSubRen
fusion-Esub-Eren : 
    {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → (e : Expr Δ₁ Γ₁ T)
  → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃)
  → let sub = subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tren T ρ* σ*) in
    sub (Esub σ* σ (Eren ρ* ρ e)) ≡ Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e

fusion-Esub-Eren {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} e ρ σ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tsub-Tren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Esub σ* σ (Eren ρ* ρ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Esub σ* σ (Eren ρ* ρ e)
    R.≅⟨ fusion-Esub-Eren' e ρ σ ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e
    R.∎
  )

--! FusionRenSub
fusion-Eren-Esub : 
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    {T : Type Δ₁ l}
    (e : Expr Δ₁ Γ₁ T)
    (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
  let sub = subst (Expr Δ₃ Γ₃) (fusion-Tren-Tsub T σ* ρ*) in
  sub (Eren ρ* ρ (Esub σ* σ e)) ≡ Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e

fusion-Eren-Esub {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} e σ ρ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tren-Tsub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Eren ρ* ρ (Esub σ* σ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Eren ρ* ρ (Esub σ* σ e)
    R.≅⟨ fusion-Eren-Esub' e σ ρ ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e
    R.∎
  )

--! FusionSubSub
fusion-Esub-Esub : 
  ∀ {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    {T : Type Δ₁ l}
    (e : Expr Δ₁ Γ₁ T)
    (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃) →
  let sub = subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tsub T σ₁* σ₂*) in
  sub (Esub σ₂* σ₂ (Esub σ₁* σ₁ e)) ≡ Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂) e

fusion-Esub-Esub {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} e σ ρ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tsub-Tsub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Esub ρ* ρ (Esub σ* σ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Esub ρ* ρ (Esub σ* σ e)
    R.≅⟨ fusion-Esub-Esub' e σ ρ ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e
    R.∎
  )
