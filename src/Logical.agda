module Logical where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_])
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

open import Extensionality
open import PropositionalSetOmegaEquality
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import TypeSubstPropertiesSem
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import BigStep

----------------------------------------------------------------------
--! Logical >

open import LogicalPrelim


--! MCVType
𝓥⟦_⟧  : (T : Type Δ l) → (ρ : 𝓓⟦ Δ ⟧) → CValue  (Tsub (π₁ ρ) T) → ⟦ T ⟧ (⟦ π₁ ρ ⟧* []) → Set l
𝓔⟦_⟧  : (T : Type Δ l) → (ρ : 𝓓⟦ Δ ⟧) → CExpr   (Tsub (π₁ ρ) T) → ⟦ T ⟧ (⟦ π₁ ρ ⟧* []) → Set l

--! MCVBody
𝓥⟦ `ℕ ⟧ ρ u z =
  ∃[ n ] (exp u ≡ # n) ∧ (n ≡ z)
𝓥⟦ T₁ ⇒ T₂ ⟧ ρ u f =
  ∃[ e ] (exp u ≡ ƛ e) ∧
  ∀ w z → 𝓥⟦ T₁ ⟧ ρ w z → 𝓔⟦ T₂ ⟧ ρ (e [ exp w ]E) (f z)
𝓥⟦ ` α ⟧ ρ v z =
  π₂ ρ _ α v (subst id (subst-var-preserves α (π₁ ρ) []) z)
𝓥⟦ `∀α l , T ⟧ ρ u F =
  ∃[ e ] (exp u ≡ Λ l ⇒ e) ∧
  ∀ T′ R →
  ∃[ v ] (e [ T′ ]ET ⇓ v)
       ∧ 𝓥⟦ T ⟧ (REext ρ (T′ , R)) (subst CValue (RE-ext∘lift ρ T T′ R) v) (F (⟦ T′ ⟧ []))

--! MCE
𝓔⟦ T ⟧ ρ e z = ∃[ v ] (e ⇓ v) ∧ 𝓥⟦ T ⟧ ρ v z


-- extended LR on environments

--! MCG
𝓖⟦_⟧ : (Γ : Ctx Δ) (ρ : RelEnv Δ) → CSub (π₁ ρ) Γ → Env Δ Γ (⟦ π₁ ρ ⟧* []) → Set (levelEnv Γ)
𝓖⟦ ∅       ⟧ ρ χ γ = ⊤
𝓖⟦ T ◁ Γ   ⟧ ρ χ γ = 𝓥⟦ T ⟧ ρ (χ _ _ here) (γ _ _ here) ∧ 𝓖⟦ Γ ⟧ ρ (Cdrop χ) (Gdrop γ)
𝓖⟦ l ◁* Γ  ⟧ ρ χ γ = 𝓖⟦ Γ ⟧ (REdrop ρ) (Cdrop-t χ) (Gdrop-t (π₁ ρ) γ)

----------------------------------------

-- subst-split-⇓ :
--   ∀ {Tₑ Tᵥ : Type [] l}
--   → (e : CExpr Tₑ)
--   → (v : CValue Tᵥ)
--   → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
--   → subst CExpr Tₑ≡Tᵥ e ⇓ v
--   → e ⇓ subst CValue (sym Tₑ≡Tᵥ) v
-- subst-split-⇓ e v refl x = x

--! substSplitEqEval
subst-split-eq-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : CExpr Tₑ)
  → (v : CValue Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst CExpr Tₑ≡Tᵥ e ⇓ v ≡ e ⇓ subst CValue (sym Tₑ≡Tᵥ) v
subst-split-eq-⇓ e v refl = refl

-- subst-split-⇓′ :
--   ∀ {Tₑ Tᵥ : Type [] l}
--   → (e : CExpr Tₑ)
--   → (v : CValue Tᵥ)
--   → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
--   → e ⇓ subst CValue (sym Tₑ≡Tᵥ) v
--   → subst CExpr Tₑ≡Tᵥ e ⇓ v
-- subst-split-⇓′ e v refl x = x

-- subst-split-⇓₂ :
--   ∀ {T T′ : Type [] l}
--   → {e : CExpr T}
--   → {v : CValue T}
--   → (T≡T′ : T ≡ T′)
--   → e ⇓ v
--   → subst CExpr T≡T′ e ⇓ subst CValue T≡T′ v
-- subst-split-⇓₂ refl e⇓v = e⇓v

subst-split-eq-⇓₂ :
  ∀ {T T′ : Type [] l}
  → {e : CExpr T}
  → {v : CValue T}
  → (T≡T′ : T ≡ T′)
  → e ⇓ v
  ≡ subst CExpr T≡T′ e ⇓ subst CValue T≡T′ v
subst-split-eq-⇓₂ refl = refl

subst-split-[]E :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁′)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → subst CExpr eq₂ (e [ subst CExpr (sym eq₁) e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ e′ ]E)
subst-split-[]E e e′ refl refl = refl

subst-split-[]E′ :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁′)
  → (eq₁ : T₁′ ≡ T₁) (eq₂ : T₂ ≡ T₂′)
  → subst CExpr eq₂ (e [ subst CExpr eq₁ e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (sym eq₁) eq₂ e [ e′ ]E)
subst-split-[]E′ e e′ refl refl = refl

subst-split-[]E″ :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ subst CExpr eq₁ e′ ]E)
  ≡ subst CExpr eq₂ (e [ e′ ]E) 
subst-split-[]E″ e e′ refl refl = refl

-- {- <-- TypeSubstProperties -}
-- σ[T′]≡↑τ*∘ext-ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l)
--   → ∀ l′ x → Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ l′ x ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′) l′ x
-- σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ here = refl
-- σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ (there x) = refl

-- σ[T′]≡↑τ*∘ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l)
--   → Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′)
-- σ[T′]≡↑τ*∘ext ρ τ* T′ = fun-ext₂ (σ[T′]≡↑τ*∘ext-ext ρ τ* T′)
-- {- --> TypeSubstProperties -}

