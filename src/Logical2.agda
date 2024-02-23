module Logical2 where

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

open import LogicalPrelim


--! MCVType
𝓥⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → Value (Tsub (π₁ ρ) T) → ⟦ T ⟧ (subst-to-env* (π₁ ρ) []) → Set l
𝓔⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → CExpr (Tsub (π₁ ρ) T) → ⟦ T ⟧ (subst-to-env* (π₁ ρ) []) → Set l

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
       ∧ 𝓥⟦ T ⟧ (REext ρ (T′ , R)) (subst Value (lemma1 ρ T T′ R) v) (F (⟦ T′ ⟧ []))

--! MCE
𝓔⟦ T ⟧ ρ e z = ∃[ v ] (e ⇓ v) ∧ 𝓥⟦ T ⟧ ρ v z

-- closing value substitution

--! CSub
CSub : TSub Δ [] → TEnv Δ → Set
CSub {Δ} σ* Γ = ∀ l (T : Type Δ l) → inn T Γ → Value (Tsub σ* T)

--! ESSC
ES←SC : {σ* : TSub Δ []} → CSub σ* Γ → ESub σ* Γ ∅
ES←SC χ = λ l T x → exp (χ l T x)

--! Csub
Csub : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → CExpr (Tsub σ* T)
Csub {σ* = σ*} χ e = Esub σ* (ES←SC χ) e

--! Cdrop
Cdrop : ∀ {l} {T : Type Δ l} → CSub σ* (T ◁ Γ) → CSub σ* Γ
Cdrop χ l T x = χ l T (there x)

--! Cextend
Cextend : ∀ {l} {T : Type Δ l} → CSub σ* Γ → Value (Tsub σ* T) → CSub σ* (T ◁ Γ)
Cextend χ v _ _ here = v
Cextend χ v _ _ (there x) = χ _ _ x

Cextend-Eext : ∀ {l} {T : Type Δ l} → (χ : CSub σ* Γ) → (w : Value (Tsub σ* T)) → 
  ES←SC (Cextend {T = T} χ w) ≡ Eextₛ _ (ES←SC χ) (exp w)
Cextend-Eext {Δ = Δ} {σ* = σ*} {Γ = Γ} {T = T} χ w =
  fun-ext (λ l → fun-ext (λ T′ → fun-ext (λ x → aux l T′ x)))
    where
      aux :  (l : Level) (T′ : Type Δ l) (x : inn T′ (T ◁ Γ)) →
        exp ((Cextend χ w) l _ x) ≡ Eextₛ σ* (ES←SC χ) (exp w) l _ x
      aux l T′ here = refl
      aux l T′ (there x) = refl

Cdrop-Cextend : ∀ {l} {σ* : TSub Δ []} {T : Type Δ l}
  → (χ : CSub σ* Γ) → (v : Value (Tsub σ* T))
  → Cdrop {l = l} {T = T} (Cextend {l = l} χ v) ≡ χ
Cdrop-Cextend {Δ = Δ} {Γ = Γ} {l = l} {T = T} χ v =
  fun-ext λ l′ → fun-ext λ T′ → fun-ext λ x → aux l′ T′ x
  where
    aux : ∀ l′ (T′ : Type Δ l′) → (x : inn T′ Γ) → Cdrop {T = T} (Cextend χ v) l′ _ x ≡ χ l′ _ x
    aux _ _ here = refl
    aux _ _ (there x) = refl
    aux _ _ (tskip x) = refl

Cdropt : {Γ : TEnv Δ} → CSub σ* (l ◁* Γ) → CSub (Tdropₛ σ*) Γ
Cdropt {σ* = σ*} χ l T x = subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) σ*) (χ _ _ (tskip x))

--! Cextt
Cextt : ∀{l} → CSub σ* Γ → (T′ : Type [] l) → CSub (Textₛ σ* T′) (l ◁* Γ)
Cextt {σ* = σ*} χ T′ _ _ (tskip {T = T} x) = subst Value (sym (σT≡TextₛσTwkT σ* T)) (χ _ _ x)

Cextt-Eextₛ-l : ∀{l} {T′ : Type [] l} → (χ : CSub σ* Γ)
  → ES←SC (Cextt χ T′) ≡ Eextₛ-l _ (ES←SC χ)
Cextt-Eextₛ-l {σ* = σ*}{T′ = T′} χ = fun-ext (λ l′ → fun-ext (λ T → fun-ext (λ x → aux l′ T x)))
  where
    aux : ∀ {T′} (l′ : Level) (T : Type _ l′) (x : inn T (l ◁* _))
      → ES←SC (Cextt χ T′) l′ T x ≡ Eextₛ-l σ* (ES←SC χ) l′ T x
    aux {T′ = T′} l′ .(Twk _) (tskip {T = T} x) =
      dist-subst' {F = Value} {G = CExpr} id exp
        (sym
          (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ σ* T′))
           (trans (sym (assoc-sub-sub T (λ z → `_) σ*))
            (trans (cong (Tsub σ*) (TidₛT≡T T)) refl))))
        (sym
          (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ σ* T′))
           (trans (sym (assoc-sub-sub T (λ z → `_) σ*))
            (trans (cong (Tsub σ*) (TidₛT≡T T)) refl))))
         (χ l′ T x)


-- extended LR on environments

--! MCG
𝓖⟦_⟧ : (Γ : TEnv Δ) → (ρ : RelEnv Δ)
  → CSub (subst←RE ρ) Γ
  → let η = subst-to-env* (subst←RE ρ) [] in Env Δ Γ η → Set (levelEnv Γ)
𝓖⟦ ∅ ⟧ ρ χ γ = ⊤
𝓖⟦ T ◁ Γ ⟧ ρ χ γ = 𝓥⟦ T ⟧ ρ (χ _ _ here) (γ _ T here)
                 ∧ 𝓖⟦ Γ ⟧ ρ (Cdrop χ) (ENVdrop Γ _ γ)
𝓖⟦ l ◁* Γ ⟧ ρ χ γ = 𝓖⟦ Γ ⟧ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ)

----------------------------------------

-- subst-split-⇓ :
--   ∀ {Tₑ Tᵥ : Type [] l}
--   → (e : CExpr Tₑ)
--   → (v : Value Tᵥ)
--   → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
--   → subst CExpr Tₑ≡Tᵥ e ⇓ v
--   → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
-- subst-split-⇓ e v refl x = x

--! substSplitEqEval
subst-split-eq-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : CExpr Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst CExpr Tₑ≡Tᵥ e ⇓ v ≡ e ⇓ subst Value (sym Tₑ≡Tᵥ) v
subst-split-eq-⇓ e v refl = refl

-- subst-split-⇓′ :
--   ∀ {Tₑ Tᵥ : Type [] l}
--   → (e : CExpr Tₑ)
--   → (v : Value Tᵥ)
--   → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
--   → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
--   → subst CExpr Tₑ≡Tᵥ e ⇓ v
-- subst-split-⇓′ e v refl x = x

-- subst-split-⇓₂ :
--   ∀ {T T′ : Type [] l}
--   → {e : CExpr T}
--   → {v : Value T}
--   → (T≡T′ : T ≡ T′)
--   → e ⇓ v
--   → subst CExpr T≡T′ e ⇓ subst Value T≡T′ v
-- subst-split-⇓₂ refl e⇓v = e⇓v

subst-split-eq-⇓₂ :
  ∀ {T T′ : Type [] l}
  → {e : CExpr T}
  → {v : Value T}
  → (T≡T′ : T ≡ T′)
  → e ⇓ v
  ≡ subst CExpr T≡T′ e ⇓ subst Value T≡T′ v
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

{- <-- TypeSubstProperties -}
σ[T′]≡↑τ*∘ext-ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) → ∀ l′ x →  Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ l′ x ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′) l′ x
σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ here = refl
σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ (there x) = refl

σ[T′]≡↑τ*∘ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) →  Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′)
σ[T′]≡↑τ*∘ext ρ τ* T′ = fun-ext₂ (σ[T′]≡↑τ*∘ext-ext ρ τ* T′)
{- --> TypeSubstProperties -}

