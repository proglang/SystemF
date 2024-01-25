module TypeSub where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Prelude
open import Type

Ren : KindCtx → KindCtx → Set
Ren Δ₁ Δ₂ = ∀ l → Δ₁ ∋ l → Δ₂ ∋ l

Sub : KindCtx → KindCtx → Set
Sub Δ₁ Δ₂ = ∀ l → Δ₁ ∋ l → Δ₂ ⊢ l

_↑ᵣ_ : Ren Δ₁ Δ₂ → ∀ l → Ren (l ∷ Δ₁) (l ∷ Δ₂)
(ρ ↑ᵣ k) _ (here x)  = here x
(ρ ↑ᵣ k) _ (there x) = there (ρ _ x)

_⋯ᵣ_ : Δ₁ ⊢ l → Ren Δ₁ Δ₂ → Δ₂ ⊢ l
`ℕ           ⋯ᵣ ρ = `ℕ
(` x)        ⋯ᵣ ρ = ` ρ _ x
(∀[α∶ l ] t) ⋯ᵣ ρ = ∀[α∶ l ] (t ⋯ᵣ (ρ ↑ᵣ l))
(t₁ ⇒ t₂)    ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)

idᵣ : Ren Δ Δ
idᵣ _ x = x 

wkᵣ' : ∀ l → Ren Δ₁ Δ₂ → Ren Δ₁ (l ∷ Δ₂)
wkᵣ' l ρ _ x = there (ρ _  x)

wkᵣ : ∀ l → Ren Δ (l ∷ Δ)
wkᵣ l _ x = there x

_↑ₛ_ : Sub Δ₁ Δ₂ → ∀ l → Sub (l ∷ Δ₁) (l ∷ Δ₂)
(σ ↑ₛ k) _ (here x)    = ` here x
(σ ↑ₛ k) _ (there x) = σ _ x ⋯ᵣ wkᵣ _

_⋯ₛ_ : Δ₁ ⊢ l → Sub Δ₁ Δ₂ → Δ₂ ⊢ l
`ℕ           ⋯ₛ σ = `ℕ
(` x)        ⋯ₛ σ = σ _ x
(∀[α∶ l ] t) ⋯ₛ σ = ∀[α∶ l ] (t ⋯ₛ (σ ↑ₛ l))
(t₁ ⇒ t₂)    ⋯ₛ σ = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)

idₛ : Sub Δ Δ
idₛ _ x = ` x 

extₛ : Δ₂ ⊢ l → Sub Δ₁ Δ₂ → Sub (l ∷ Δ₁) Δ₂
extₛ t σ _ (here refl) = t
extₛ t σ _ (there x) = σ _ x

dropₛ :  Sub (l ∷ Δ₁) Δ₂ → Sub Δ₁ Δ₂
dropₛ σ _ x = σ _ (there x)

⦅_⦆ₛ : Δ ⊢ l → Sub (l ∷ Δ) Δ
⦅ t ⦆ₛ = extₛ t idₛ 

_[_] : (l₁ ∷ Δ) ⊢ l → Δ ⊢ l₁ → Δ ⊢ l
t [ t₁ ] = t ⋯ₛ ⦅ t₁ ⦆ₛ
