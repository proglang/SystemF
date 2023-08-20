module SmallStep where

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

open import Ext
open import SetOmega
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution

-- small step call by value semantics

data Val : Expr Δ Γ T → Set where
  v-n : Val {Δ}{Γ} (# n)
  v-ƛ : Val (ƛ e)
  v-Λ : Val (Λ l ⇒ e)


data _↪_ : Expr Δ Γ T → Expr Δ Γ T → Set where
  β-ƛ : 
     Val e₂ →
     ((ƛ e₁) · e₂) ↪ (e₁ [ e₂ ]E)
  β-Λ : ∀  {l l′ : Level} {T : Type Δ l} {T′ : Type (l ∷ Δ) l′} {e : Expr (l ∷ Δ) (l ◁* Γ) T′} →
     ((Λ l ⇒ e) ∙ T) ↪ (e [ T ]ET)
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : 
    e₂ ↪ e → 
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ : ∀ {l l′ : Level} {T′ : Type Δ l′} {T : Type (l′ ∷ Δ) l} {e₁ e₂ : Expr Δ Γ (`∀α l′ , T)} →
    e₁ ↪ e₂ →
    (e₁ ∙ T′) ↪ (e₂ ∙ T′)
