module Expr where

open import Level using (Level; zero; suc)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)

open import Prelude
open import Type 
open import TypeSub

data _∍_ : TypeCtx Δ  → Δ ⊢ l → Set where
  here  : (t ∷ Γ) ∍ t 
  there : Γ ∍ t → (t' ∷ Γ) ∍ t
  skip  : Γ ∍ t → (l ∷⋆ Γ) ∍ (t ⋯ᵣ wkᵣ _)

variable
  x x₁ x₂ x₃ x' x₁' x₂' x₃' : Γ ∍ t
  n n₁ n₂ n₃ n' n₁' n₂' n₃' : ℕ
  
data _⍮_⊢_ : (Δ : KindCtx) → TypeCtx Δ → Δ ⊢ l → Set where
  #_ :
    (n : ℕ) →
    Δ ⍮ Γ ⊢ `ℕ
  `_ :
    Γ ∍ t →
    Δ ⍮ Γ ⊢ t
  λx_ :
    Δ ⍮ (t₁ ∷ Γ) ⊢ t₂ →
    Δ ⍮ Γ        ⊢ (t₁ ⇒ t₂)
  Λ[α∶_]_ :
    (l : Level) →
    {t : (l ∷ Δ) ⊢ l'} →  
    (l ∷ Δ) ⍮ (l ∷⋆ Γ) ⊢ t →
    Δ       ⍮ Γ        ⊢ (∀[α∶ l ] t)
  _·_ :
    Δ ⍮ Γ ⊢ (t₁ ⇒ t₂) →
    Δ ⍮ Γ ⊢ t₁ →
    Δ ⍮ Γ ⊢ t₂
  _∙_ :
    Δ ⍮ Γ ⊢ (∀[α∶ l ] t) →
    (t' : Δ ⊢ l) →
    Δ ⍮ Γ ⊢ (t ⋯ₛ ⦅ t' ⦆ₛ)

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Δ ⍮ Γ ⊢ t
  
