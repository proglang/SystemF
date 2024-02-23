{-# OPTIONS --allow-unsolved-metas #-}
module LogicalVariation where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; -- Properties
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import BigStep

----------------------------------------------------------------------
--! Logical >
--! Variation >

open import LogicalPrelim

-- stratified logical relation

postulate
  useful-eq : ∀ (T : Type (l ∷ Δ) l′) (ρ : RelEnv Δ) (T′ : Type [] l) (R : REL T′)
    → let ρ′ = REext ρ (T′ , R)
    in Tsub (π₁ ρ′) T ≡ Tsub (Tliftₛ (π₁ ρ) l) T [ T′ ]T

--! MCVType
𝓥′⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ) → REL (Tsub (π₁ ρ) T)

--! MCEType
𝓔′⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → CExpr (Tsub (π₁ ρ) T) → ⟦ Tsub (π₁ ρ) T ⟧ [] → Set l

--! MCVBody
𝓥′⟦ ` α ⟧ ρ v z =
  π₂ ρ _ α v z
𝓥′⟦ T₁ ⇒ T₂ ⟧ ρ u f =
  ∃[ e ] (exp u ≡ ƛ e) ∧
  ∀ w z → 𝓥′⟦ T₁ ⟧ ρ w z → 𝓔′⟦ T₂ ⟧ ρ (e [ exp w ]E) (f z)
𝓥′⟦ `∀α l , T ⟧ ρ u F =
  ∃[ e ] (exp u ≡ Λ l ⇒ e) ∧
  ∀ T′ R → let ρ′ = REext ρ (T′ , R) in 
  ∃[ v ] (subst CExpr (sym (useful-eq T ρ T′ R)) (e [ T′ ]ET) ⇓ v)
       ∧ 𝓥′⟦ T ⟧ ρ′ v (subst id (sym (trans (cong (λ t → ⟦ t ⟧ []) (useful-eq T ρ T′ R))
                                           {!!})) -- Tsingle-subst-preserves [] T′ T
                               (F (⟦ T′ ⟧ [])))
𝓥′⟦ `ℕ ⟧ ρ u z =
  ∃[ n ] (exp u ≡ (# n)) ∧ (n ≡ z)

--! MCE
𝓔′⟦ T ⟧ ρ e z = ∃[ v ] (e ⇓ v) ∧ 𝓥′⟦ T ⟧ ρ v z
