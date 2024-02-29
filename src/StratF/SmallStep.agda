module StratF.SmallStep where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.BigStep
open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.Util.Extensionality
open import StratF.Util.PropositionalSetOmegaEquality

-- small step call by value semantics

--! SmallStep >

--! SingleReduction
data _↪_ : Expr Δ Γ T → Expr Δ Γ T → Set where

  β-ƛ : 
    isValue e₂ →
    ((ƛ e₁) · e₂) ↪ (e₁ [ e₂ ]E)
  β-Λ : ∀ {T : Type Δ l} {T′ : Type (l ∷ Δ) l′} {e : Expr (l ∷ Δ) (l ◁* Γ) T′} →
    ((Λ l ⇒ e) ∙ T) ↪ (e [ T ]ET)
  β-suc :
    `suc {Γ = Γ} (# n) ↪ (# (suc n))
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : 
    e₂ ↪ e → 
    isValue e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ : ∀ {T′ : Type Δ l′} {T : Type (l′ ∷ Δ) l} {e₁ e₂ : Expr Δ Γ (`∀α l′ , T)} →
    e₁ ↪ e₂ →
    (e₁ ∙ T′) ↪ (e₂ ∙ T′)
  ξ-suc :
    e₁ ↪ e →
    `suc e₁ ↪ `suc e

--! Reduction
data _—↠_ : Expr Δ Γ T → Expr Δ Γ T → Set where

  —↠-refl :
    e —↠ e
  —↠-step :
    e₁ ↪ e₂ →
    e₂ —↠ e₃ →
    e₁ —↠ e₃

--! Trans
—↠-trans : e₁ —↠ e₂ → e₂ —↠ e₃ → e₁ —↠ e₃
—↠-trans —↠-refl e₂—↠e₃ = e₂—↠e₃
—↠-trans (—↠-step e₁↪e₂ e₁—↠e₂) e₂—↠e₃ = —↠-step e₁↪e₂ (—↠-trans e₁—↠e₂ e₂—↠e₃)
