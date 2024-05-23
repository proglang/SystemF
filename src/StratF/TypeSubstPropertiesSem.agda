-- This file contains definitions and lemmas about semantic renamings
-- and substitutions of types.

module StratF.TypeSubstPropertiesSem where

open import Level
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.Types
open import StratF.TypeSubstitution
open import StratF.TypeSubstProperties
open import StratF.Util.Extensionality
open import StratF.Util.PropositionalSetOmegaEquality

private variable
  ρ ρ₁ ρ₂ ρ′ : TSub Δ₁ Δ₂
  σ σ₁ σ₂ σ′ : TSub Δ₁ Δ₂

--! TF >

-- the action of renaming on semantic environments

TRen* : (ρ* : TRen Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
TRen* {Δ₁} ρ* η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ* _ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → TRen* (Twkᵣ {Δ₁ = Δ}{l = l} Tidᵣ) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

Tren*-id : (η : Env* Δ) → TRen* Tidᵣ η η
Tren*-id η x = refl

Tren*-pop : (ρ* : TRen (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → 
  TRen* ρ* (α ∷ η₁) η₂ → TRen* (λ _ x → ρ* _ (there x)) η₁ η₂
Tren*-pop ρ* α η₁ η₂ Tren* x = Tren* (there x)

Tren*-lift : ∀ {ρ* : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → TRen* ρ* η₁ η₂ → TRen* (Tliftᵣ ρ* _) (α ∷ η₁) (α ∷ η₂)
Tren*-lift α Tren* here = refl
Tren*-lift α Tren* (there x) = Tren* x

--! RenPreservesSemanticsType
Tren*-preserves-semantics : (Tren* : TRen* ρ* η₁ η₂) →
  (T : Type Δ₁ l) → ⟦ Tren ρ* T ⟧ η₂ ≡ ⟦ T ⟧ η₁

Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (` x) = Tren* x
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (T₁ ⇒ T₂) = cong₂ (λ A₁ A₂ → A₁ → A₂) (Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* T₁) (Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* T₂)
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (`∀α l , T) = dep-ext λ where 
  α → Tren*-preserves-semantics{ρ* = Tliftᵣ ρ* _}{α ∷ η₁}{α ∷ η₂} (Tren*-lift {ρ* = ρ*} α Tren*) T
Tren*-preserves-semantics Tren* `ℕ = refl

-- special case of composition sub o ren

sublemma-ext : (σ : TSub Δ []) → ∀ l x → (Textₛ σ T) l x ≡ (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T) l x
sublemma-ext σ l here = refl
sublemma-ext{T = T} σ l (there x) =
  trans (sym (TidₛT≡T (σ l x)))
        (sym (fusion-Tsub-Tren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T)))

sublemma : (σ : TSub Δ []) → (Textₛ σ T) ≡ Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T
sublemma {T = T} σ = fun-ext₂ (sublemma-ext σ)

lemma2 : (σ : TSub Δ []) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l)
  → Tsub (Tliftₛ σ l) T [ T′ ]T ≡ Tsub (Textₛ σ T′) T
lemma2 σ T T′ = begin 
    Tsub (Textₛ Tidₛ T′) (Tsub (Tliftₛ σ _) T)
  ≡⟨ fusion-Tsub-Tsub T (Tliftₛ σ _) (Textₛ Tidₛ T′) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T′) T
  ≡⟨ cong (λ σ → Tsub σ T) (sym (sublemma σ)) ⟩
    Tsub (Textₛ σ T′) T
  ∎

Tdrop-σ≡Twk∘σ : ∀ (σ* : TSub (l ∷ Δ₁) Δ₂) → Tdropₛ σ* ≡ Twkᵣ Tidᵣ ∘ᵣₛ σ*
Tdrop-σ≡Twk∘σ σ* = fun-ext₂ (λ x y → refl)

-- the action of substitution on semantic environments

--! substToEnv
⟦_⟧* : TSub Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
⟦_⟧* {Δ₁ = []}     σ* η₂ = []
⟦_⟧* {Δ₁ = _ ∷ _}  σ* η₂ = ⟦ σ* _ here ⟧ η₂ ∷ ⟦ Tdropₛ σ* ⟧* η₂

subst-to-env* : TSub Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
subst-to-env* = ⟦_⟧*

--! substVarPreservesType
subst-var-preserves : (α : l ∈ Δ₁) (τ* : TSub Δ₁ Δ₂) 
  (η₂ : Env* Δ₂) → lookup α (⟦ τ* ⟧* η₂) ≡ ⟦ τ* l α ⟧ η₂

subst-var-preserves here σ* η₂ = refl
subst-var-preserves (there x) σ* η₂ = subst-var-preserves x (Tdropₛ σ*) η₂

subst-to-env*-wk : (σ*  : TSub Δ₁ Δ₂) → (α  : Set l) → (η₂ : Env* Δ₂) → 
  subst-to-env* (Twkₛ σ*) (α ∷ η₂) ≡ω subst-to-env* σ* η₂
subst-to-env*-wk {Δ₁ = []} σ* α η₂ = refl
subst-to-env*-wk {Δ₁ = l ∷ Δ₁} σ* α η₂ = transω (conglω (_∷ subst-to-env* (Tdropₛ (Twkₛ σ*)) (α ∷ η₂)) (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) (σ* _ here)))
                                               (congωω (⟦ (σ* _ here) ⟧ η₂ ∷_) (subst-to-env*-wk (Tdropₛ σ*) α η₂))

subst-to-env*-build : ∀ (ρ* : TRen Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ* η₁ η₂
  → subst-to-env* (λ _ x → ` ρ* _ x) η₂ ≡ω η₁
subst-to-env*-build ρ* [] η₂ Tren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ* (α ∷ η₁) η₂ Tren* = 
  transω (congωω (λ H → apply-env η₂ (ρ* _ here) ∷ H) (subst-to-env*-build (λ _ x → ρ* _ (there x)) η₁ η₂ (Tren*-pop ρ* α η₁ η₂ Tren*)))
         (conglω (_∷ η₁) (Tren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* Tidₛ η ≡ω η
subst-to-env*-id {Δ = Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ _ x → x) η η (Tren*-id η)

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ* : TSub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ Tsub σ* T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ* η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ* (` x) =
  sym (subst-var-preserves x σ* η₂)
subst-preserves {η₂ = η₂} σ* (T₁ ⇒ T₂) =
  cong₂ (λ A B → A → B) (subst-preserves{η₂ = η₂} σ* T₁) (subst-preserves{η₂ = η₂} σ* T₂)
subst-preserves {η₂ = η₂} σ* (`∀α l , T) =
  dep-ext (λ ⟦α⟧ →
    trans (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ* _) T)
          (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ* ⟦α⟧ η₂)))
subst-preserves σ* `ℕ = refl
 
--! SingleSubstPreserves
Tsingle-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) 
  (T : Type (l ∷ Δ) l′) → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)

Tsingle-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (Textₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

subst-to-env*-comp : (σ* : TSub Δ₁ Δ₂) → (τ* : TSub Δ₂ Δ₃) → (η : Env* Δ₃) → subst-to-env* σ* (subst-to-env* τ* η) ≡ω subst-to-env* (σ* ∘ₛₛ τ*) η
subst-to-env*-comp {Δ₁ = []} σ* τ* η = refl
subst-to-env*-comp {Δ₁ = l ∷ Δ₁} σ* τ* η = conglωω _∷_ (sym (subst-preserves τ* (σ* l here))) (subst-to-env*-comp (Tdropₛ σ*) τ* η)

apply-env-var : (σ* : TSub Δ []) (x : l ∈ Δ) → apply-env (subst-to-env* σ* []) x ≡ ⟦ σ* l x ⟧ []
apply-env-var σ* here = refl
apply-env-var σ* (there x) = apply-env-var (Tdropₛ σ*) x

τ*∈Ren* : (τ* : TRen Δ₁ Δ₂) (σ* : TSub Δ₂ []) → TRen* τ* (subst-to-env* (τ* ∘ᵣₛ σ*) []) (subst-to-env* σ* [])
τ*∈Ren* τ* σ* here = apply-env-var σ* (τ* _ here)
τ*∈Ren* τ* σ* (there x) = τ*∈Ren* (Tdropᵣ τ*) σ* x
