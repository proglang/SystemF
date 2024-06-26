-- This file contains the definitions for expression renamings and
-- substitutions and related operations like lifting and composition.

module StratF.ExprSubstitution where

open import Level
open import Data.List using (List; []; _∷_)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.Expressions
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types

--! Sub >

-- expression renamings

--! DefERen
ERen : TRen Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ERen {Δ₁}{Δ₂} ρ* Γ₁ Γ₂ = ∀ l (T : Type Δ₁ l) → inn T Γ₁ → inn (Tren ρ* T) Γ₂

--! DefEidR
Eidᵣ : ERen Tidᵣ Γ Γ 
Eidᵣ l T x = subst (λ T → inn T _) (sym (TidᵣT≡T T)) x

Edropᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* (T ◁ Γ₁) Γ₂ → ERen ρ* Γ₁ Γ₂
Edropᵣ ρ* ρ l T x = ρ _ _ (there x)

Ewkᵣ : ∀ {l} {T : Type Δ₂ l} → (ρ* : TRen Δ₁ Δ₂) → ERen ρ* Γ₁ Γ₂ → ERen ρ* Γ₁ (T ◁ Γ₂) 
Ewkᵣ ρ* ρ l T x = there (ρ _ _ x) 

Eliftᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* Γ₁ Γ₂ → ERen ρ* (T ◁ Γ₁) (Tren ρ* T ◁ Γ₂)
Eliftᵣ ρ* ρ _ _ here = here
Eliftᵣ ρ* ρ _ _ (there x) = there (ρ _ _ x)

Eliftᵣ-l : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* Γ₁ Γ₂ → ERen (Tliftᵣ ρ* l) (l ◁* Γ₁) (l ◁* Γ₂)
Eliftᵣ-l {Γ₂ = Γ₂} {l = l} ρ* ρ _ _ (tskip x) = subst id (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _))) (tskip (ρ _ _ x))

--! DefEren
Eren : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tren ρ* T)

Eren ρ* ρ (# n) = # n
Eren ρ* ρ (`suc e) = `suc (Eren ρ* ρ e)
Eren ρ* ρ (` x) = ` ρ _ _ x
Eren ρ* ρ (ƛ e) = ƛ Eren ρ* (Eliftᵣ ρ* ρ) e
Eren ρ* ρ (e₁ · e₂) = Eren ρ* ρ e₁ · Eren ρ* ρ e₂
Eren ρ* ρ (Λ l ⇒ e) = Λ l ⇒ Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) e
Eren {Δ₂ = Δ₂} {Γ₂ = Γ₂} {T = .(T [ T′ ]T)} ρ* ρ (_∙_ {T = T} e T′) = 
  subst (Expr Δ₂ Γ₂) (sym (swap-Tren-[] ρ* T T′)) (Eren ρ* ρ e ∙ Tren ρ* T′)

Ewk : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) T 
Ewk {T = T} e = subst (λ T → Expr _ _ T) (TidᵣT≡T T) (Eren _ (Ewkᵣ Tidᵣ Eidᵣ) e)

Ewkᵣ-l : ∀ (l : Level) → ERen (Twkᵣ Tidᵣ) Γ (l ◁* Γ)
Ewkᵣ-l l _ _ = tskip

Ewk-l : Expr Δ Γ T → Expr (l ∷ Δ) (l ◁* Γ) (Twk T)  
Ewk-l e = Eren _ (Ewkᵣ-l _) e

-- expression substitutions

--! DefESub
ESub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ESub {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ* Γ₁ Γ₂ = 
  ∀ l (T : Type Δ₁ l) → inn T Γ₁ → Expr Δ₂ Γ₂ (Tsub σ* T)

--! DefEidS
Eidₛ : ESub Tidₛ Γ Γ
Eidₛ _ T x = subst (Expr _ _) (sym (TidₛT≡T T)) (` x)
-- Eidₛ _ T rewrite TidₛT≡T T = `_

Ewkₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub σ* Γ₁ (T ◁ Γ₂)
Ewkₛ σ* σ _ T x = Ewk (σ _ T x)

Edropₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* (T ◁ Γ₁) Γ₂ → ESub σ* Γ₁ Γ₂
Edropₛ σ* σ _ _ x = σ _ _ (there x)

--! DefEsub
Esub      :  (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → 
             Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tsub σ* T)
Eliftₛ    :  (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → 
             ESub σ* (T ◁ Γ₁) (Tsub σ* T ◁ Γ₂)
Eliftₛ-l  :  (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → 
             ESub (Tliftₛ σ* l) (l ◁* Γ₁) (l ◁* Γ₂)

Eliftₛ _ σ _ _ here = ` here
Eliftₛ _ σ _ _ (there x) = Ewk (σ _ _ x)

Eliftₛ-l σ* σ _ _ (tskip {T = T} x) = subst (Expr _ _) (sym (swap-Tsub-Twk σ* T)) (Ewk-l (σ _ _ x))

Esub σ* σ (# n) = # n
Esub σ* σ (`suc e) = `suc (Esub σ* σ e)
Esub σ* σ (` x) = σ _ _ x
Esub σ* σ (ƛ e) = ƛ Esub σ* (Eliftₛ σ* σ) e
Esub σ* σ (e₁ · e₂) = Esub σ* σ e₁ · Esub σ* σ e₂
Esub σ* σ (Λ l ⇒ e) = Λ l ⇒ Esub (Tliftₛ σ* _) (Eliftₛ-l σ* σ) e
Esub σ* σ (_∙_ {T = T} e T′) = subst (Expr _ _) (sym (swap-Tsub-[] σ* T T′)) (Esub σ* σ e ∙ (Tsub σ* T′))

Eextₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → Expr Δ₂ Γ₂ (Tsub σ* T) → ESub σ* (T ◁ Γ₁) Γ₂
Eextₛ σ* σ e' _ _ here = e'
Eextₛ σ* σ e' _ _ (there x) = σ _ _ x

Eextₛ-l : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub (Textₛ σ* T) (l ◁* Γ₁) Γ₂
Eextₛ-l {Δ₂ = Δ₂} {Γ₂ = Γ₂} σ* σ _ _ (tskip {T = T} x) = subst (Expr Δ₂ Γ₂) (sym (σT≡TextₛσTwkT σ* T)) (σ _ _ x) 

_[_]E : Expr Δ (T₁ ◁ Γ) T₂ → Expr Δ Γ T₁ → Expr Δ Γ T₂
_[_]E {T₁ = T₁} {T₂ = T₂} e e′ = 
  subst (Expr _ _) (TidₛT≡T T₂) (Esub Tidₛ (Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T T₁)) e′)) e)

_[_]ET : Expr (l ∷ Δ) (l ◁* Γ) T → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)
e [ T′ ]ET = Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ) e

sub0 : Expr Δ Γ (Tsub Tidₛ T₁) → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0 e′ = Eextₛ Tidₛ Eidₛ e′

sub0′ : Expr Δ Γ T₁ → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0′ e′ = Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T _)) e′)

-- composition of expression substitutions and renamings

--! DefECompositionRR
_>>RR_ : ∀ {Δ₁}{Δ₂}{Δ₃}{ρ₁* : TRen Δ₁ Δ₂} {ρ₂* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ERen ρ₁* Γ₁ Γ₂ → ERen ρ₂* Γ₂ Γ₃ → ERen (ρ₁* ∘ᵣᵣ ρ₂*) Γ₁ Γ₃
_>>RR_ {Δ₃ = Δ₃}{ρ₁* = ρ₁*}{ρ₂* = ρ₂*}{Γ₃ = Γ₃} ρ₁ ρ₂ l T x
  = subst (λ T → inn T Γ₃) (fusion-Tren-Tren T ρ₁* ρ₂*) (ρ₂ _ _ (ρ₁ _ _ x))

--! DefECompositionRS
_>>RS_ : ∀ {Δ₁}{Δ₂}{Δ₃}{ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ERen ρ* Γ₁ Γ₂ → ESub σ* Γ₂ Γ₃ → ESub (ρ* ∘ᵣₛ σ*) Γ₁ Γ₃
_>>RS_ {Δ₃ = Δ₃}{ρ* = ρ*}{σ* = σ*}{Γ₃ = Γ₃} ρ σ l T x
  = subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tren T ρ* σ*) (σ _ _ (ρ _ _ x))

--! DefECompositionSR
_>>SR_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ* Γ₁ Γ₂ → ERen ρ* Γ₂ Γ₃ → ESub (σ* ∘ₛᵣ ρ*) Γ₁ Γ₃
_>>SR_ {Δ₃ = Δ₃}{σ* = σ*}{ρ* = ρ*}{Γ₃ = Γ₃} σ ρ l T x
  = subst (Expr Δ₃ Γ₃) (fusion-Tren-Tsub T σ* ρ*) (Eren ρ* ρ (σ _ _ x))

--! DefECompositionSS
_>>SS_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ₁* Γ₁ Γ₂ → ESub σ₂* Γ₂ Γ₃ → ESub (σ₁* ∘ₛₛ σ₂*) Γ₁ Γ₃
_>>SS_ {Δ₃ = Δ₃}{σ₁* = σ₁*}{σ₂* = σ₂*}{Γ₃ = Γ₃} σ₁ σ₂ l T x
  = subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tsub T σ₁* σ₂*) (Esub _ σ₂ (σ₁ _ _ x))
