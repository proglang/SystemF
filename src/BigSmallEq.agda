module BigSmallEq where

open import Level renaming (suc to lsuc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Extensionality
open import PropositionalSetOmegaEquality
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import SmallStep
open import BigStep

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
`ξ-·₂ —↠-refl          isV = —↠-refl
`ξ-·₂ (—↠-step e₁↪e e₂—↠e₁) isV = —↠-step (ξ-·₂ e₁↪e isV) (`ξ-·₂ e₂—↠e₁ isV)

`β-ƛ : isValue e₂ → (e₁ —↠ (ƛ e)) → (e₁ · e₂) —↠ (e [ e₂ ]E)
`β-ƛ isV —↠-refl           = —↠-step (β-ƛ isV) —↠-refl
`β-ƛ isV (—↠-step e₁↪e₂ e₂—↠ƛe) = —↠-step (ξ-·₁ e₁↪e₂) (`β-ƛ isV e₂—↠ƛe)

⇓to—↠ :
  e ⇓ v →
  e —↠ exp v
⇓to—↠ ⇓-n                                 = —↠-refl 
⇓to—↠ (⇓-s e⇓#n)                          = `β-suc (⇓to—↠ e⇓#n)
⇓to—↠ ⇓-ƛ = —↠-refl
⇓to—↠ (⇓-· {v₂ = v₂} e₁⇓ƛe e₂⇓v' e[e₂]⇓v) = —↠-trans (`ξ-·₁ (⇓to—↠ e₁⇓ƛe)) (—↠-trans (`ξ-·₂ (⇓to—↠  e₂⇓v') V-ƛ) (—↠-step (β-ƛ (prf v₂)) (⇓to—↠ e[e₂]⇓v)))
⇓to—↠ ⇓-Λ                                 = —↠-refl
⇓to—↠ (⇓-∙ e₁⇓Λe e₂[T]⇓v)                 = —↠-trans (`β-Λ (⇓to—↠ e₁⇓Λe)) (⇓to—↠ e₂[T]⇓v)
  