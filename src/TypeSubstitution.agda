module TypeSubstitution where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Types
open import Ext

--! Sub >

-- renaming on types

--! DefTRen
TRen : LEnv → LEnv → Set
TRen Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → l ∈ Δ₂

variable 
  ρ* ρ*₁ ρ*₂ : TRen Δ₁ Δ₂

--! DefTidR
Tidᵣ : TRen Δ Δ

Tidᵣ _ = id

Tdropᵣ : TRen (l ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
Tdropᵣ ρ* _ x = ρ* _ (there x)

Twkᵣ : TRen Δ₁ Δ₂ → TRen Δ₁ (l ∷ Δ₂)
Twkᵣ ρ* _ x = there (ρ* _ x)

--! DefTliftR
Tliftᵣ : TRen Δ₁ Δ₂ → ∀ l → TRen (l ∷ Δ₁) (l ∷ Δ₂)

Tliftᵣ ρ* _ _ here = here
Tliftᵣ ρ* _ _ (there x) = there (ρ* _ x)

--! DefTren
Tren : TRen Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)

Tren ρ* (` x) = ` ρ* _ x
Tren ρ* (T₁ ⇒ T₂) = Tren ρ* T₁ ⇒ Tren ρ* T₂
Tren ρ* (`∀α l , T) = `∀α l , Tren (Tliftᵣ ρ* l) T
Tren ρ* `ℕ = `ℕ

Twk : Type Δ l′ → Type (l ∷ Δ) l′
Twk = Tren (Twkᵣ Tidᵣ)

-- substitution on types

--! DefTSub
TSub : LEnv → LEnv → Set
TSub Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → Type Δ₂ l

variable 
  σ* σ*₁ σ*₂ : TSub Δ₁ Δ₂
 
--! DefTidS
Tidₛ : TSub Δ Δ

Tidₛ _ = `_

Tdropₛ : TSub (l ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
Tdropₛ σ* _ x = σ* _ (there x)

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (l ∷ Δ₂)
Twkₛ σ* _ x = Twk (σ* _ x)

--! DefTliftS
Tliftₛ : TSub Δ₁ Δ₂ → ∀ l → TSub (l ∷ Δ₁) (l ∷ Δ₂)  

Tliftₛ σ* _ _ here = ` here
Tliftₛ σ* _ _ (there x) = Twk (σ* _ x)

--! DefTsub
Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l

Tsub σ* (` x) = σ* _ x
Tsub σ* (T₁ ⇒ T₂) = Tsub σ* T₁ ⇒ Tsub σ* T₂
Tsub σ* (`∀α l , T) = `∀α l , Tsub (Tliftₛ σ* _) T
Tsub σ* `ℕ = `ℕ

Textₛ : TSub Δ₁ Δ₂ → Type Δ₂ l → TSub (l ∷ Δ₁) Δ₂
Textₛ σ* T' _ here = T'
Textₛ σ* T' _ (there x) = σ* _ x

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = Tsub (Textₛ Tidₛ T') T

-- composition of renamings and substitutions

--! DefTCompositionRR
_∘ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ ∘ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

--! DefTCompositionRS
_∘ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(ρ ∘ᵣₛ σ) _ x = σ _ (ρ _ x)

--! DefTCompositionSR
_∘ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ ∘ₛᵣ ρ) _ x = Tren ρ (σ _ x)

--! DefTCompositionSS
_∘ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ₁ ∘ₛₛ σ₂) _ x = Tsub σ₂ (σ₁ _ x)
