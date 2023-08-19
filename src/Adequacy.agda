{-# OPTIONS --allow-unsolved-metas #-}
module Adequacy where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Ext
open import SmallStep
open import SetOmega

subst-to-env : {σ* : TSub Δ₁ Δ₂} → ESub σ* Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ* η₂)
subst-to-env {η₂ = η₂} {σ* = σ*} σ γ₂ _ T x = subst id (subst-preserves σ* T) (E⟦ σ _ x ⟧ η₂ γ₂)

Esubst-preserves : ∀ {T : Type Δ₁ l} {η₂ : Env* Δ₂} {γ₂ : Env Δ₂ Γ₂ η₂} {σ* : TSub Δ₁ Δ₂} 
  → (σ : ESub σ* Γ₁ Γ₂) (e : Expr Δ₁ Γ₁ T)
  → E⟦ Esub σ* σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ* T)) (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))
Esubst-preserves σ (# n) = refl
Esubst-preserves σ (` x) = {!   !}
Esubst-preserves σ (ƛ e) = {!   !}
Esubst-preserves σ (e₁ · e₂) = {!   !}
Esubst-preserves σ (Λ l ⇒ e) = {!   !}
Esubst-preserves σ (e ∙ T′) = {!   !}