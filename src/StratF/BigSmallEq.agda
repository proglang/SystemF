module StratF.BigSmallEq where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)

open import StratF.BigStep
open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.SmallStep
open import StratF.Types

--! SmallStep >

`ξ-suc : e₁ —↠ e → `suc e₁ —↠ `suc e
`ξ-suc —↠-refl               = —↠-refl
`ξ-suc (—↠-step e₁↪e₂ e₂—↠e) = —↠-step (ξ-suc e₁↪e₂) (`ξ-suc e₂—↠e)

`β-suc : e₁ —↠ (# n) → `suc e₁ —↠ (# suc n)
`β-suc —↠-refl                = —↠-step β-suc —↠-refl
`β-suc (—↠-step e₁↪e₂ e₂—↠#n) = —↠-step (ξ-suc e₁↪e₂) (`β-suc e₂—↠#n)

`ξ-∙ : e₁ —↠ e → (e₁ ∙ T′) —↠ (e ∙ T′)
`ξ-∙ —↠-refl               = —↠-refl
`ξ-∙ (—↠-step e₁↪e₂ e₂—↠e) = —↠-step (ξ-∙ e₁↪e₂) (`ξ-∙ e₂—↠e)

`β-Λ : e₁ —↠ (Λ l ⇒ e) → (e₁ ∙ T) —↠ (e [ T ]ET)
`β-Λ —↠-refl                = —↠-step β-Λ —↠-refl
`β-Λ (—↠-step e₁↪e₂ e₂—↠Λe) = —↠-step (ξ-∙ e₁↪e₂) (`β-Λ e₂—↠Λe)

`ξ-·₁ : e₁ —↠ e → (e₁ · e₂) —↠ (e · e₂)
`ξ-·₁ —↠-refl               = —↠-refl
`ξ-·₁ (—↠-step e₁↪e₂ e₂—↠e) = —↠-step (ξ-·₁ e₁↪e₂) (`ξ-·₁ e₂—↠e)

`ξ-·₂ : e₂ —↠ e → isValue e₁ → (e₁ · e₂) —↠ (e₁ · e)
`ξ-·₂ —↠-refl          isV      = —↠-refl
`ξ-·₂ (—↠-step e₁↪e e₂—↠e₁) isV = —↠-step (ξ-·₂ e₁↪e isV) (`ξ-·₂ e₂—↠e₁ isV)

`β-ƛ : isValue e₂ → (e₁ —↠ (ƛ e)) → (e₁ · e₂) —↠ (e [ e₂ ]E)
`β-ƛ isV —↠-refl                = —↠-step (β-ƛ isV) —↠-refl
`β-ƛ isV (—↠-step e₁↪e₂ e₂—↠ƛe) = —↠-step (ξ-·₁ e₁↪e₂) (`β-ƛ isV e₂—↠ƛe)

----------------------------------------------------------------------
-- big step API

infix 15 _↓_
--! BigAPI
_↓_ : ∀ {T : Type [] l} → CExpr T → CValue T → Set
e ↓ v = e —↠ exp v

--! BigAPIFunctions
↓-n : # n ↓ (# n , V-♯)
↓-s : e ↓ (# n , V-♯) → `suc e ↓ (# suc n , V-♯)
↓-ƛ : ƛ e ↓ (ƛ e , V-ƛ)
↓-· : e₁ ↓ (ƛ e , V-ƛ) → e₂ ↓ v₂ → (e [ exp v₂ ]E) ↓ v → (e₁ · e₂) ↓ v
↓-Λ : Λ l ⇒ e ↓ (Λ l ⇒ e , V-Λ)
↓-∙ : e₁ ↓ (Λ l ⇒ e , V-Λ) → (e [ T ]ET) ↓ v → (e₁ ∙ T) ↓ v
Value-↓ : ∀ {T : Type [] l} → (v : CValue T) → exp v ↓ v

--! BigN
↓-n = —↠-refl

--! BigS
↓-s —↠-refl = —↠-step β-suc  —↠-refl
↓-s (—↠-step e₁↪e₂ e↓n) = —↠-step (ξ-suc e₁↪e₂) (↓-s e↓n)

--! BigLam
↓-ƛ = —↠-refl

--! BigApp
↓-· {v₂ = v₂} e₁↓ƛe e₂↓v₂ e[v₂]↓v =
  —↠-trans (`ξ-·₁ e₁↓ƛe) (—↠-trans (`ξ-·₂ e₂↓v₂ V-ƛ) (—↠-step (β-ƛ (prf v₂)) e[v₂]↓v))

--! BigLAM
↓-Λ = —↠-refl

--! BigAPP
↓-∙ e₁↓Λe e₂[T]↓v = —↠-trans (`β-Λ e₁↓Λe) e₂[T]↓v

--! ValueReduceSelf
Value-↓ ((# n) , V-♯) = ↓-n
Value-↓ ((ƛ _) , V-ƛ) = ↓-ƛ
Value-↓ ((Λ l ⇒ _) , V-Λ) = ↓-Λ

----------------------------------------------------------------------

--! BigToSmall
⇓to—↠ :
  e ⇓ v →
  e —↠ exp v
⇓to—↠ ⇓-n        = ↓-n
⇓to—↠ (⇓-s e⇓#n) = ↓-s (⇓to—↠ e⇓#n)
⇓to—↠ ⇓-ƛ        = ↓-ƛ
⇓to—↠ (⇓-· {v₂ = v₂} {v = v} e₁⇓ƛe e₂⇓v' e[e₂]⇓v)
                  = ↓-· {v₂ = v₂} {v = v} (⇓to—↠ e₁⇓ƛe) (⇓to—↠  e₂⇓v') (⇓to—↠ e[e₂]⇓v)
⇓to—↠ ⇓-Λ        = ↓-Λ
⇓to—↠ (⇓-∙ {v = v} e₁⇓Λe e₂[T]⇓v)
                  = ↓-∙ {v = v} (⇓to—↠ e₁⇓Λe) (⇓to—↠ e₂[T]⇓v)

