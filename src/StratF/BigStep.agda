module StratF.BigStep where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)

open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.Types
open import StratF.Evaluation

--! BigStep >

-- big step semantics
infix 15 _⇓_
--! Semantics
data _⇓_ : CExpr T → CValue T → Set where
  ⇓-n  :  # n ⇓ (# n , V-♯)
  ⇓-s  :  e ⇓ (# n , V-♯) → `suc e ⇓ (# suc n , V-♯)
  ⇓-ƛ  :  ƛ e ⇓ (ƛ e , V-ƛ)
  ⇓-·  :  e₁ ⇓ (ƛ e , V-ƛ) → e₂ ⇓ v₂ → (e [ exp v₂ ]E) ⇓ v →
          (e₁ · e₂) ⇓ v
  ⇓-Λ  :  Λ l ⇒ e ⇓ (Λ l ⇒ e , V-Λ)
  ⇓-∙  :  e₁ ⇓ (Λ l ⇒ e , V-Λ) → (e [ T ]ET) ⇓ v → (e₁ ∙ T) ⇓ v

--! ValueReduceSelf
Value-⇓ : ∀ {l} {T : Type [] l} → (v : CValue T) → exp v ⇓ v
Value-⇓ (.(# _) ,      V-♯)  = ⇓-n
Value-⇓ (.(ƛ _) ,      V-ƛ)  = ⇓-ƛ
Value-⇓ (.(Λ _ ⇒ _) ,  V-Λ)  = ⇓-Λ

-- evaluation API
--! evalBig
evalBig : Eval
evalBig = record
            { _↓_ = _⇓_
            ; ↓-n = ⇓-n
            ; ↓-s = ⇓-s
            ; ↓-ƛ = ⇓-ƛ
            ; ↓-· = ⇓-·
            ; ↓-Λ = ⇓-Λ
            ; ↓-∙ = ⇓-∙
            ; Value-↓ = Value-⇓
            }
