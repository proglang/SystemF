module TypeSubProp where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude
open import Type
open import TypeSub

_ᵣ·ᵣ_ : Δ₁ ⇒ᵣ Δ₂ → Δ₂ ⇒ᵣ Δ₃ → Δ₁ ⇒ᵣ Δ₃
(ρ₁ ᵣ·ᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

↑ᵣ-dist-ᵣ·ᵣ : ∀ (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (ρ₁ ↑ᵣ l) ᵣ·ᵣ (ρ₂ ↑ᵣ l) ≡ (ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣ l
↑ᵣ-dist-ᵣ·ᵣ ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ᵣᵣ-fusion : ∀ (t : Δ₁ ⊢ l) (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (t ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ t ⋯ᵣ (ρ₁ ᵣ·ᵣ ρ₂)
⋯ᵣᵣ-fusion `ℕ           ρ₁ ρ₂ = refl
⋯ᵣᵣ-fusion (` x)        ρ₁ ρ₂ = refl
⋯ᵣᵣ-fusion (t₁ ⇒ t₂)    ρ₁ ρ₂ = cong₂ _⇒_ (⋯ᵣᵣ-fusion t₁ ρ₁ ρ₂) (⋯ᵣᵣ-fusion t₂ ρ₁ ρ₂)
⋯ᵣᵣ-fusion (∀[α∶ l ] t) ρ₁ ρ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ᵣ (ρ₁ ↑ᵣ l)) ⋯ᵣ (ρ₂ ↑ᵣ l)
  ≡⟨ ⋯ᵣᵣ-fusion t (ρ₁ ↑ᵣ l) (ρ₂ ↑ᵣ l) ⟩
    t ⋯ᵣ ((ρ₁ ↑ᵣ l) ᵣ·ᵣ (ρ₂ ↑ᵣ l))
  ≡⟨ cong (t ⋯ᵣ_) (↑ᵣ-dist-ᵣ·ᵣ ρ₁ ρ₂) ⟩
    t ⋯ᵣ ((ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣ l)
  ∎)


_ᵣ·ₛ_ : Δ₁ ⇒ᵣ Δ₂ → Δ₂ ⇒ₛ Δ₃ → Δ₁ ⇒ₛ Δ₃
(ρ₁ ᵣ·ₛ σ₂) _ x = σ₂ _ (ρ₁ _ x)

↑ₛ-dist-ᵣ·ₛ : ∀ (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (σ₂ : Δ₂ ⇒ₛ Δ₃) →
  (ρ₁ ↑ᵣ l) ᵣ·ₛ (σ₂ ↑ₛ l) ≡ (ρ₁ ᵣ·ₛ σ₂) ↑ₛ l
↑ₛ-dist-ᵣ·ₛ ρ₁ σ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ᵣₛ-fusion : ∀ (t : Δ₁ ⊢ l) (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (σ₂ : Δ₂ ⇒ₛ Δ₃) →
  (t ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ t ⋯ₛ (ρ₁ ᵣ·ₛ σ₂)
⋯ᵣₛ-fusion `ℕ           ρ₁ σ₂ = refl
⋯ᵣₛ-fusion (` x)        ρ₁ σ₂ = refl
⋯ᵣₛ-fusion (t₁ ⇒ t₂)    ρ₁ σ₂ = cong₂ _⇒_ (⋯ᵣₛ-fusion t₁ ρ₁ σ₂) (⋯ᵣₛ-fusion t₂ ρ₁ σ₂)
⋯ᵣₛ-fusion (∀[α∶ l ] t) ρ₁ σ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ᵣ (ρ₁ ↑ᵣ l)) ⋯ₛ (σ₂ ↑ₛ l)
  ≡⟨ ⋯ᵣₛ-fusion t (ρ₁ ↑ᵣ l) (σ₂ ↑ₛ l) ⟩
    t ⋯ₛ ((ρ₁ ↑ᵣ l) ᵣ·ₛ (σ₂ ↑ₛ l))
  ≡⟨ cong (t ⋯ₛ_) (↑ₛ-dist-ᵣ·ₛ ρ₁ σ₂) ⟩
    t ⋯ₛ ((ρ₁ ᵣ·ₛ σ₂) ↑ₛ l)
  ∎)


_ₛ·ᵣ_ : Δ₁ ⇒ₛ Δ₂ → Δ₂ ⇒ᵣ Δ₃ → Δ₁ ⇒ₛ Δ₃
(σ₁ ₛ·ᵣ ρ₂) _ x = σ₁ _ x ⋯ᵣ ρ₂

↑ₛ-dist-ₛ·ᵣ : ∀ (σ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (σ₁ ↑ₛ l) ₛ·ᵣ (ρ₂ ↑ᵣ l) ≡ (σ₁ ₛ·ᵣ ρ₂) ↑ₛ l
↑ₛ-dist-ₛ·ᵣ {l = l} σ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) →
    begin
      ((σ₁ ↑ₛ l) ₛ·ᵣ (ρ₂ ↑ᵣ l)) _ (suc x)
    ≡⟨⟩
      (σ₁ _ x ⋯ᵣ wkᵣ l) ⋯ᵣ (ρ₂ ↑ᵣ l)
    ≡⟨ ⋯ᵣᵣ-fusion (σ₁ _ x) (wkᵣ l) (ρ₂ ↑ᵣ l) ⟩
      σ₁ _ x ⋯ᵣ (wkᵣ l ᵣ·ᵣ (ρ₂ ↑ᵣ l))
    ≡⟨ cong (σ₁ _ x ⋯ᵣ_) refl ⟩
      σ₁ _ x ⋯ᵣ (ρ₂ ᵣ·ᵣ wkᵣ l)
    ≡⟨ sym (⋯ᵣᵣ-fusion (σ₁ _ x) ρ₂ (wkᵣ l)) ⟩
      (σ₁ _ x ⋯ᵣ ρ₂) ⋯ᵣ wkᵣ l
    ≡⟨⟩
      ((σ₁ ₛ·ᵣ ρ₂) _ x ⋯ᵣ wkᵣ l)
    ∎

⋯ₛᵣ-fusion : ∀ (t : Δ₁ ⊢ l) (σ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (t ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ t ⋯ₛ (σ₁ ₛ·ᵣ ρ₂)
⋯ₛᵣ-fusion `ℕ           σ₁ ρ₂ = refl
⋯ₛᵣ-fusion (` x)        σ₁ ρ₂ = refl
⋯ₛᵣ-fusion (t₁ ⇒ t₂)    σ₁ ρ₂ = cong₂ _⇒_ (⋯ₛᵣ-fusion t₁ σ₁ ρ₂) (⋯ₛᵣ-fusion t₂ σ₁ ρ₂)
⋯ₛᵣ-fusion (∀[α∶ l ] t) σ₁ ρ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ₛ (σ₁ ↑ₛ l)) ⋯ᵣ (ρ₂ ↑ᵣ l)
  ≡⟨ ⋯ₛᵣ-fusion t (σ₁ ↑ₛ l) (ρ₂ ↑ᵣ l) ⟩
    t ⋯ₛ ((σ₁ ↑ₛ l) ₛ·ᵣ (ρ₂ ↑ᵣ l))
  ≡⟨ cong (t ⋯ₛ_) (↑ₛ-dist-ₛ·ᵣ σ₁ ρ₂) ⟩
    t ⋯ₛ ((σ₁ ₛ·ᵣ ρ₂) ↑ₛ l)
  ∎)


_ₛ·ₛ_ : Δ₁ ⇒ₛ Δ₂ → Δ₂ ⇒ₛ Δ₃ → Δ₁ ⇒ₛ Δ₃
(ρ₁ ₛ·ₛ ρ₂) _ x = ρ₁ _ x ⋯ₛ ρ₂

↑ₛ-dist-ₛ·ₛ : ∀ (ρ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ₛ Δ₃) →
  (ρ₁ ↑ₛ l) ₛ·ₛ (ρ₂ ↑ₛ l) ≡ (ρ₁ ₛ·ₛ ρ₂) ↑ₛ l
↑ₛ-dist-ₛ·ₛ {l = l} ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) →
    begin
      ((ρ₁ ↑ₛ l) ₛ·ₛ (ρ₂ ↑ₛ l)) _ (suc x)
    ≡⟨⟩
      (ρ₁ _ x ⋯ᵣ wkᵣ l) ⋯ₛ (ρ₂ ↑ₛ l)
    ≡⟨ ⋯ᵣₛ-fusion (ρ₁ _ x) (wkᵣ l) (ρ₂ ↑ₛ l) ⟩
      ρ₁ _ x ⋯ₛ (wkᵣ l ᵣ·ₛ (ρ₂ ↑ₛ l))
    ≡⟨ cong (ρ₁ _ x ⋯ₛ_) refl ⟩
      ρ₁ _ x ⋯ₛ (ρ₂ ₛ·ᵣ wkᵣ l)
    ≡⟨ sym (⋯ₛᵣ-fusion (ρ₁ _ x) ρ₂ (wkᵣ l)) ⟩
      (ρ₁ _ x ⋯ₛ ρ₂) ⋯ᵣ wkᵣ l
    ≡⟨⟩
      ((ρ₁ ₛ·ₛ ρ₂) _ x ⋯ᵣ wkᵣ l)
    ∎

⋯ₛₛ-fusion : ∀ (t : Δ₁ ⊢ l) (σ₁ : Δ₁ ⇒ₛ Δ₂) (σ₂ : Δ₂ ⇒ₛ Δ₃) →
  (t ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ t ⋯ₛ (σ₁ ₛ·ₛ σ₂)
⋯ₛₛ-fusion `ℕ           σ₁ σ₂ = refl
⋯ₛₛ-fusion (` x)        σ₁ σ₂ = refl
⋯ₛₛ-fusion (t₁ ⇒ t₂)    σ₁ σ₂ = cong₂ _⇒_ (⋯ₛₛ-fusion t₁ σ₁ σ₂) (⋯ₛₛ-fusion t₂ σ₁ σ₂)
⋯ₛₛ-fusion (∀[α∶ l ] t) σ₁ σ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ₛ (σ₁ ↑ₛ l)) ⋯ₛ (σ₂ ↑ₛ l)
  ≡⟨ ⋯ₛₛ-fusion t (σ₁ ↑ₛ l) (σ₂ ↑ₛ l) ⟩
    t ⋯ₛ ((σ₁ ↑ₛ l) ₛ·ₛ (σ₂ ↑ₛ l))
  ≡⟨ cong (t ⋯ₛ_) (↑ₛ-dist-ₛ·ₛ σ₁ σ₂) ⟩
    t ⋯ₛ ((σ₁ ₛ·ₛ σ₂) ↑ₛ l)
  ∎)

idᵣ-↑ᵣ : idᵣ ↑ᵣ l ≡ idᵣ {Δ = l ∷ Δ}
idᵣ-↑ᵣ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ᵣ-id : ∀ (t : Δ ⊢ l) →
  t ⋯ᵣ idᵣ ≡ t
⋯ᵣ-id `ℕ           = refl
⋯ᵣ-id (` x)        = refl
⋯ᵣ-id (∀[α∶ l ] t) = cong ∀[α∶ l ]_ (
  begin
     t ⋯ᵣ (idᵣ ↑ᵣ l)
   ≡⟨ cong (t ⋯ᵣ_) idᵣ-↑ᵣ ⟩
     t ⋯ᵣ idᵣ
   ≡⟨ ⋯ᵣ-id t ⟩
     t
   ∎)
⋯ᵣ-id (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯ᵣ-id t₁) (⋯ᵣ-id t₂)

wkᵣ-↑ᵣ : ∀ (t : Δ₁ ⊢ l') (ρ : Δ₁ ⇒ᵣ Δ₂) →
  (t ⋯ᵣ ρ) ⋯ᵣ wkᵣ l ≡ (t ⋯ᵣ wkᵣ l) ⋯ᵣ (ρ ↑ᵣ l)
wkᵣ-↑ᵣ {Δ₁} {k'} {Δ₂} {l} t ρ =
  begin
    (t ⋯ᵣ ρ) ⋯ᵣ wkᵣ l
  ≡⟨ ⋯ᵣᵣ-fusion t ρ (wkᵣ l) ⟩
    t ⋯ᵣ (ρ ᵣ·ᵣ wkᵣ l)
  ≡⟨⟩
    t ⋯ᵣ (wkᵣ l ᵣ·ᵣ (ρ ↑ᵣ l))
  ≡⟨ sym (⋯ᵣᵣ-fusion t (wkᵣ l) (ρ ↑ᵣ l)) ⟩
    (t ⋯ᵣ wkᵣ l) ⋯ᵣ (ρ ↑ᵣ l)
  ∎

wkᵣ-↑ₛ : ∀ (t : Δ₁ ⊢ l') (σ : Δ₁ ⇒ₛ Δ₂) →
  (t ⋯ₛ σ) ⋯ᵣ wkᵣ l ≡ (t ⋯ᵣ wkᵣ l) ⋯ₛ (σ ↑ₛ l)
wkᵣ-↑ₛ {Δ₁} {k'} {Δ₂} {l} t ρ =
  begin
    (t ⋯ₛ ρ) ⋯ᵣ wkᵣ l
  ≡⟨ ⋯ₛᵣ-fusion t ρ (wkᵣ l) ⟩
    t ⋯ₛ (ρ ₛ·ᵣ wkᵣ l)
  ≡⟨⟩
    t ⋯ₛ (wkᵣ l ᵣ·ₛ (ρ ↑ₛ l))
  ≡⟨ sym (⋯ᵣₛ-fusion t (wkᵣ l) (ρ ↑ₛ l)) ⟩
    (t ⋯ᵣ wkᵣ l) ⋯ₛ (ρ ↑ₛ l)
  ∎

idₛ-↑ₛ : idₛ ↑ₛ l ≡ idₛ {Δ = l ∷ Δ}
idₛ-↑ₛ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ₛ-id : ∀ (t : Δ ⊢ l) →
  t ⋯ₛ idₛ ≡ t
⋯ₛ-id `ℕ           = refl
⋯ₛ-id (` x)        = refl
⋯ₛ-id (∀[α∶ l ] t) = cong ∀[α∶ l ]_ (
  begin
     t ⋯ₛ (idₛ ↑ₛ l)
   ≡⟨ cong (t ⋯ₛ_) idₛ-↑ₛ ⟩
     t ⋯ₛ idₛ
   ≡⟨ ⋯ₛ-id t ⟩
     t
   ∎)
⋯ₛ-id (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯ₛ-id t₁) (⋯ₛ-id t₂)

wkᵣ-cancels-⦅⦆ₛ : ∀ (t' : Δ ⊢ l') (t : Δ ⊢ l) →
  (t' ⋯ᵣ wkᵣ l) ⋯ₛ ⦅ t ⦆ₛ ≡ t'
wkᵣ-cancels-⦅⦆ₛ {Δ} {k'} {l} t' t =
  begin
    (t' ⋯ᵣ wkᵣ l) ⋯ₛ ⦅ t ⦆ₛ
  ≡⟨ ⋯ᵣₛ-fusion t' (wkᵣ l) ⦅ t ⦆ₛ ⟩
    t' ⋯ₛ (wkᵣ l ᵣ·ₛ ⦅ t ⦆ₛ)
  ≡⟨⟩
    t' ⋯ₛ idₛ
  ≡⟨ ⋯ₛ-id t' ⟩
    t'
  ∎
  
wkᵣ-cancels-extₛ : ∀ (t' : Δ₁ ⊢ l') (t : Δ₂ ⊢ l) (σ : Δ₁ ⇒ₛ Δ₂) →
  ((t' ⋯ᵣ wkᵣ l) ⋯ₛ (extₛ t σ)) ≡ t' ⋯ₛ σ
wkᵣ-cancels-extₛ {l = l} t' t σ = 
  begin
    (t' ⋯ᵣ wkᵣ l) ⋯ₛ extₛ t σ
  ≡⟨ ⋯ᵣₛ-fusion t' (wkᵣ l) (extₛ t σ) ⟩
    t' ⋯ₛ (wkᵣ l ᵣ·ₛ extₛ t σ)
  ≡⟨ sym (⋯ₛₛ-fusion t' idₛ σ) ⟩
    (t' ⋯ₛ idₛ) ⋯ₛ σ
  ≡⟨ cong (_⋯ₛ σ) (⋯ₛ-id t') ⟩
    (t' ⋯ₛ σ)
  ∎

⦅⦆ₛ-↑ᵣ' : ∀ (t : Δ₁ ⊢ l) (ρ : Δ₁ ⇒ᵣ Δ₂) →
  (ρ ↑ᵣ l) ᵣ·ₛ ⦅ t ⋯ᵣ ρ ⦆ₛ ≡ ⦅ t ⦆ₛ ₛ·ᵣ ρ
⦅⦆ₛ-↑ᵣ' {Δ₁} {l} {Δ₂} t ρ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⦅⦆ₛ-↑ᵣ : ∀ (t : (l ∷ Δ₁) ⊢ l') (t' : Δ₁ ⊢ l) (ρ : Δ₁ ⇒ᵣ Δ₂) →
  (t ⋯ᵣ (ρ ↑ᵣ l)) ⋯ₛ ⦅ t' ⋯ᵣ ρ ⦆ₛ ≡ (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ᵣ ρ
⦅⦆ₛ-↑ᵣ {l} {Δ₁} {l'} {Δ₂} t t' ρ =
  begin
    (t ⋯ᵣ (ρ ↑ᵣ l)) ⋯ₛ ⦅ t' ⋯ᵣ ρ ⦆ₛ
  ≡⟨ ⋯ᵣₛ-fusion t (ρ ↑ᵣ l) ⦅ t' ⋯ᵣ ρ ⦆ₛ ⟩
    t ⋯ₛ ((ρ ↑ᵣ l) ᵣ·ₛ ⦅ t' ⋯ᵣ ρ ⦆ₛ)
  ≡⟨ cong (t ⋯ₛ_) (⦅⦆ₛ-↑ᵣ' t' ρ) ⟩
    t ⋯ₛ (⦅ t' ⦆ₛ ₛ·ᵣ ρ)
  ≡⟨ sym (⋯ₛᵣ-fusion t ⦅ t' ⦆ₛ ρ) ⟩
    (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ᵣ ρ
  ∎

⦅⦆ₛ-↑ₛ' : ∀ (t : Δ₁ ⊢ l) (σ : Δ₁ ⇒ₛ Δ₂) →
  (σ ↑ₛ l) ₛ·ₛ ⦅ t ⋯ₛ σ ⦆ₛ ≡ ⦅ t ⦆ₛ ₛ·ₛ σ
⦅⦆ₛ-↑ₛ' {Δ₁} {l} {Δ₂} t σ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → wkᵣ-cancels-⦅⦆ₛ ((⦅ t ⦆ₛ ₛ·ₛ σ) _ (suc x)) (t ⋯ₛ σ)

⦅⦆ₛ-↑ₛ : ∀ (t : (l ∷ Δ₁) ⊢ l') (t' : Δ₁ ⊢ l) (σ : Δ₁ ⇒ₛ Δ₂) →
  (t ⋯ₛ (σ ↑ₛ l)) ⋯ₛ ⦅ t' ⋯ₛ σ ⦆ₛ ≡ (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ₛ σ
⦅⦆ₛ-↑ₛ {l} {Δ₁} {k'} {Δ₂} t t' σ =
  begin
    (t ⋯ₛ (σ ↑ₛ l)) ⋯ₛ ⦅ t' ⋯ₛ σ ⦆ₛ
  ≡⟨ ⋯ₛₛ-fusion t (σ ↑ₛ l) ⦅ t' ⋯ₛ σ ⦆ₛ ⟩
    t ⋯ₛ ((σ ↑ₛ l) ₛ·ₛ ⦅ t' ⋯ₛ σ ⦆ₛ)
  ≡⟨ cong (t ⋯ₛ_) (⦅⦆ₛ-↑ₛ' t' σ) ⟩
    t ⋯ₛ (⦅ t' ⦆ₛ ₛ·ₛ σ)
  ≡⟨ sym (⋯ₛₛ-fusion t ⦅ t' ⦆ₛ σ) ⟩
    (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ₛ σ
  ∎ 