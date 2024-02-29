module StratF.TypeSubstProperties where

open import Level
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.Util.Extensionality

private variable
  ρ ρ₁ ρ₂ ρ′ : TSub Δ₁ Δ₂
  σ σ₁ σ₂ σ′ : TSub Δ₁ Δ₂

--! TF >

-- interaction of renamings and substituions

sub↑-dist-∘ᵣₛ : ∀ l (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
  Tliftₛ (ρ ∘ᵣₛ σ) _ ≡ Tliftᵣ ρ l ∘ᵣₛ Tliftₛ σ _ 
sub↑-dist-∘ᵣₛ l ρ σ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

mutual 
  fusion-Tsub-Tren-lift : ∀ (T : Type (l ∷ Δ₁) l′) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ _) (Tren (Tliftᵣ ρ _) T) ≡ Tsub (Tliftₛ (ρ ∘ᵣₛ σ) _) T
  fusion-Tsub-Tren-lift T ρ σ = begin
      Tsub (Tliftₛ σ _) (Tren (Tliftᵣ ρ _) T) 
    ≡⟨ fusion-Tsub-Tren T (Tliftᵣ ρ _) (Tliftₛ σ _) ⟩
      Tsub (Tliftᵣ ρ _ ∘ᵣₛ Tliftₛ σ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ᵣₛ _ ρ σ)) ⟩
      Tsub (Tliftₛ (ρ ∘ᵣₛ σ) _) T
    ∎

  --! FusionSubRen
  fusion-Tsub-Tren : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub σ (Tren ρ T) ≡ Tsub (ρ ∘ᵣₛ σ) T

  fusion-Tsub-Tren (` x) ρ σ = refl
  fusion-Tsub-Tren (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (fusion-Tsub-Tren T₁ ρ σ) (fusion-Tsub-Tren T₂ ρ σ)
  fusion-Tsub-Tren (`∀α l , T) ρ σ = cong (`∀α l ,_) (fusion-Tsub-Tren-lift T ρ σ)
  fusion-Tsub-Tren `ℕ ρ σ = refl

ren↑-dist-∘ᵣᵣ : ∀ l (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
  Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _ ≡ ((Tliftᵣ ρ₁ l) ∘ᵣᵣ (Tliftᵣ ρ₂ _)) 
ren↑-dist-∘ᵣᵣ l ρ₁ ρ₂ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

mutual 
  fusion-Tren-Tren-lift : ∀ (T : Type (l ∷ Δ₁) l′) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ₂ _) (Tren (Tliftᵣ ρ₁ _) T) ≡ Tren (Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _) T
  fusion-Tren-Tren-lift {l = l} T ρ₁ ρ₂ =
      Tren (Tliftᵣ ρ₂ _) (Tren (Tliftᵣ ρ₁ _) T) 
    ≡⟨ fusion-Tren-Tren T (Tliftᵣ ρ₁ _) (Tliftᵣ ρ₂ _) ⟩
      Tren (Tliftᵣ ρ₁ _ ∘ᵣᵣ Tliftᵣ ρ₂ _) T
    ≡⟨ cong (λ ρ → Tren ρ T) (sym (ren↑-dist-∘ᵣᵣ l ρ₁ ρ₂))  ⟩
      Tren (Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _) T
    ∎

  --! FusionRenRen
  fusion-Tren-Tren : ∀ (T : Type Δ₁ l) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren ρ₂ (Tren ρ₁ T) ≡ Tren (ρ₁ ∘ᵣᵣ ρ₂) T

  fusion-Tren-Tren (` x) ρ₁ ρ₂ = refl
  fusion-Tren-Tren (T₁ ⇒ T₂) ρ₁ ρ₂ = cong₂ _⇒_ (fusion-Tren-Tren T₁ ρ₁ ρ₂) (fusion-Tren-Tren T₂ ρ₁ ρ₂)
  fusion-Tren-Tren (`∀α l , T) ρ₁ ρ₂ = cong (`∀α l ,_) (fusion-Tren-Tren-lift T ρ₁ ρ₂)
  fusion-Tren-Tren `ℕ ρ₁ ρ₂ = refl

--! SwapTrenTwk
swap-Tren-Twk : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type Δ₁ l′) → Tren (Tliftᵣ ρ l) (Twk T) ≡ Twk (Tren ρ T) 

swap-Tren-Twk {l = l} ρ T = 
  begin 
    Tren (Tliftᵣ ρ _) (Tren (Twkᵣ Tidᵣ) T)
  ≡⟨ fusion-Tren-Tren T (Twkᵣ Tidᵣ) (Tliftᵣ ρ _) ⟩
    Tren ((Twkᵣ Tidᵣ) ∘ᵣᵣ Tliftᵣ ρ _) T
  ≡⟨ sym (fusion-Tren-Tren T ρ (Twkᵣ Tidᵣ)) ⟩
    Tren (Twkᵣ Tidᵣ) (Tren ρ T)
  ∎

ren↑-dist-∘ₛᵣ : ∀ l (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
  Tliftₛ (σ ∘ₛᵣ ρ) l ≡ (Tliftₛ σ l ∘ₛᵣ Tliftᵣ ρ _)
ren↑-dist-∘ₛᵣ l σ ρ = fun-ext₂ λ where 
   _ here → refl
   _ (there x) → sym (swap-Tren-Twk ρ (σ _ x))

mutual 
  fusion-Tren-Tsub-lift : ∀ (T : Type (l ∷ Δ₁) l′) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ _) (Tsub (Tliftₛ σ _) T) ≡ Tsub (Tliftₛ (σ ∘ₛᵣ ρ) _) T
  fusion-Tren-Tsub-lift {l = l} T σ ρ = begin 
      Tren (Tliftᵣ ρ _) (Tsub (Tliftₛ σ _) T)
    ≡⟨ fusion-Tren-Tsub T (Tliftₛ σ _) (Tliftᵣ ρ _) ⟩
      Tsub (Tliftₛ σ _ ∘ₛᵣ Tliftᵣ ρ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (ren↑-dist-∘ₛᵣ l σ ρ)) ⟩
      Tsub (Tliftₛ (σ ∘ₛᵣ ρ) _) T
    ∎ 

  --! FusionRenSub
  fusion-Tren-Tsub : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren ρ (Tsub σ T) ≡ Tsub (σ ∘ₛᵣ ρ) T

  fusion-Tren-Tsub (` x) ρ σ = refl
  fusion-Tren-Tsub (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (fusion-Tren-Tsub T₁ ρ σ) (fusion-Tren-Tsub T₂ ρ σ)
  fusion-Tren-Tsub (`∀α l , T) ρ σ = cong (`∀α l ,_) (fusion-Tren-Tsub-lift T ρ σ)
  fusion-Tren-Tsub `ℕ ρ σ = refl

--! SwapTsubTwk
swap-Tsub-Twk : ∀ (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l′) → Tsub (Tliftₛ σ l) (Twk T) ≡ Twk (Tsub σ T)

swap-Tsub-Twk σ T = 
  begin 
    Tsub (Tliftₛ σ _) (Twk T) 
  ≡⟨ fusion-Tsub-Tren T (Twkᵣ Tidᵣ) (Tliftₛ σ _) ⟩
    Tsub (σ ∘ₛᵣ λ _ → there) T
  ≡⟨ sym (fusion-Tren-Tsub T σ (Twkᵣ Tidᵣ)) ⟩
    Twk (Tsub σ T)
  ∎

sub↑-dist-∘ₛₛ : ∀ l (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
  Tliftₛ (σ₁ ∘ₛₛ σ₂) _  ≡ (Tliftₛ σ₁ l ∘ₛₛ Tliftₛ σ₂ _)
sub↑-dist-∘ₛₛ l σ₁ σ₂ = fun-ext₂ λ where 
  _ here → refl
  l′ (there x) → begin 
        (Tliftₛ (σ₁ ∘ₛₛ σ₂) l) l′ (there x) 
      ≡⟨ sym (swap-Tsub-Twk {l = l} σ₂ (σ₁ l′ x)) ⟩
        (Tliftₛ σ₁ _ ∘ₛₛ Tliftₛ σ₂ _) l′ (there x)
      ∎

mutual 
  fusion-Tsub-Tsub-lift : ∀ (T : Type (l ∷ Δ₁) l′) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ₂ _) (Tsub (Tliftₛ σ₁ _) T) ≡ Tsub (Tliftₛ (σ₁ ∘ₛₛ σ₂) _) T
  fusion-Tsub-Tsub-lift {l = l} T σ₁ σ₂ = begin 
      Tsub (Tliftₛ σ₂ _) (Tsub (Tliftₛ σ₁ _) T)
    ≡⟨ fusion-Tsub-Tsub T (Tliftₛ σ₁ _) (Tliftₛ σ₂ _) ⟩
      Tsub (Tliftₛ σ₁ _ ∘ₛₛ Tliftₛ σ₂ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ l σ₁ σ₂)) ⟩
      Tsub (Tliftₛ (σ₁ ∘ₛₛ σ₂) _) T
    ∎ 

  --! FusionSubSub
  fusion-Tsub-Tsub : ∀ (T : Type Δ₁ l) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub σ₂ (Tsub σ₁ T) ≡ Tsub (σ₁ ∘ₛₛ σ₂) T

  fusion-Tsub-Tsub (` x) σ₁ σ₂ = refl
  fusion-Tsub-Tsub (T₁ ⇒ T₂) σ₁ σ₂ = cong₂ _⇒_ (fusion-Tsub-Tsub T₁ σ₁ σ₂) (fusion-Tsub-Tsub T₂ σ₁ σ₂)
  fusion-Tsub-Tsub (`∀α l , T) σ₁ σ₂ = cong (`∀α l ,_) (fusion-Tsub-Tsub-lift T σ₁ σ₂)
  fusion-Tsub-Tsub `ℕ σ₁ σ₂ = refl

TliftᵣTidᵣ≡Tidᵣ : ∀ Δ l →
  (Tliftᵣ {Δ₁ = Δ} Tidᵣ l) ≡ Tidᵣ
TliftᵣTidᵣ≡Tidᵣ _ _ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → refl

--! TidRNeutral
TidᵣT≡T : ∀ (T : Type Δ l) → Tren Tidᵣ T ≡ T

TidᵣT≡T (` x) = refl
TidᵣT≡T (T₁ ⇒ T₂) = cong₂ _⇒_ (TidᵣT≡T T₁) (TidᵣT≡T T₂)
TidᵣT≡T {Δ = Δ} (`∀α l , T) = cong (`∀α l ,_) (trans (cong (λ ρ → Tren ρ T) (TliftᵣTidᵣ≡Tidᵣ Δ l)) (TidᵣT≡T T))
TidᵣT≡T `ℕ = refl

ρ[T]≡[ρT]ρ↑ : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) →
  Textₛ Tidₛ T ∘ₛᵣ ρ ≡ (Tliftᵣ ρ _) ∘ᵣₛ Textₛ Tidₛ (Tren ρ T)
ρ[T]≡[ρT]ρ↑ T ρ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

--! SwapTrenSingle
swap-Tren-[] : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tren ρ (T [ T′ ]T) ≡ Tren (Tliftᵣ ρ _) T [ Tren ρ T′ ]T 

swap-Tren-[] ρ T T′ = begin 
    Tren ρ (T [ T′ ]T)
  ≡⟨ fusion-Tren-Tsub T (Textₛ Tidₛ T′) ρ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛᵣ ρ) T
  ≡⟨ cong (λ σ → Tsub σ T) (ρ[T]≡[ρT]ρ↑ T′ ρ) ⟩
    Tsub ((Tliftᵣ ρ _) ∘ᵣₛ (Textₛ Tidₛ (Tren ρ T′))) T
  ≡⟨ sym (fusion-Tsub-Tren T (Tliftᵣ ρ _) (Textₛ Tidₛ (Tren ρ T′))) ⟩
    Tsub (Textₛ Tidₛ (Tren ρ T′)) (Tren (Tliftᵣ ρ _) T)
  ∎

TliftₛTidₛ≡Tidₛ : ∀ Δ l →                         
  (Tliftₛ {Δ₁ = Δ} Tidₛ l) ≡ Tidₛ
TliftₛTidₛ≡Tidₛ _ _ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → refl             

--! TidSNeutral
TidₛT≡T : ∀ (T : Type Δ l) → Tsub Tidₛ T ≡ T       

TidₛT≡T (` x) = refl
TidₛT≡T (T₁ ⇒ T₂) = cong₂ _⇒_ (TidₛT≡T T₁) (TidₛT≡T T₂)
TidₛT≡T {Δ = Δ} (`∀α l , T) = cong (`∀α l ,_) (trans (cong (λ σ → Tsub σ T) (TliftₛTidₛ≡Tidₛ Δ l)) (TidₛT≡T T))
TidₛT≡T `ℕ = refl

σ[T]≡[σT]σ↑ : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) →
  (Textₛ Tidₛ T ∘ₛₛ σ) ≡ ((Tliftₛ σ _) ∘ₛₛ (Textₛ Tidₛ (Tsub σ T)))
σ[T]≡[σT]σ↑ T σ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → begin 
        σ _ x
      ≡⟨ sym (TidₛT≡T (σ _ x)) ⟩
        Tsub Tidₛ (σ _ x)
      ≡⟨ sym (fusion-Tsub-Tren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ (Tsub σ T))) ⟩
        Tsub (Textₛ Tidₛ (Tsub σ T)) (Twk (σ _ x))
      ∎

∘ᵣₛ-neutralˡ : ∀ (σ : TSub Δ₁ Δ₂) → Tidᵣ ∘ᵣₛ σ ≡ σ
∘ᵣₛ-neutralˡ σ = refl

∘ₛᵣ-neutralˡ : ∀ (σ : TSub Δ₁ Δ₂) → σ ∘ₛᵣ Tidᵣ ≡ σ
∘ₛᵣ-neutralˡ σ = fun-ext λ l → fun-ext λ x → TidᵣT≡T (σ l x)

TSub-id-left :  ∀ (σ* : TSub Δ₁ Δ₂) → (Tidₛ ∘ₛₛ σ*) ≡ σ*
TSub-id-left {Δ₁} σ* = refl

TSub-id-right : ∀ (σ* : TSub Δ₁ Δ₂) → (σ* ∘ₛₛ Tidₛ) ≡ σ*
TSub-id-right {Δ₁ = Δ₁} σ* = fun-ext₂ λ l x → TidₛT≡T (σ* l x)

--! SwapTsubSingle
swap-Tsub-[] : ∀ (σ : TSub Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tsub σ (T [ T′ ]T) ≡ (Tsub (Tliftₛ σ l) T) [ Tsub σ T′ ]T  

swap-Tsub-[] σ T T′ = 
  begin 
    Tsub σ (T [ T′ ]T) 
  ≡⟨ fusion-Tsub-Tsub T (Textₛ Tidₛ T′) σ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛₛ σ) T
  ≡⟨ cong (λ σ → Tsub σ T) (σ[T]≡[σT]σ↑ T′ σ) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ (Tsub σ T′)) T
  ≡⟨ sym (fusion-Tsub-Tsub T (Tliftₛ σ _) (Textₛ Tidₛ (Tsub σ T′))) ⟩
    (Tsub (Tliftₛ σ _) T) [ Tsub σ T′ ]T
  ∎

Twkᵣ∘Textₛ : {T′ : Type Δ₂ l′} (σ : TSub Δ₁ Δ₂) → Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′ ≡ σ
Twkᵣ∘Textₛ {T′ = T′} σ =
  begin
    (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′)
  ≡⟨ refl ⟩
    σ
  ∎

σT≡TextₛσTwkT : {T′ : Type Δ₂ l′} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) → Tsub (Textₛ σ T′) (Twk T) ≡ Tsub σ T
σT≡TextₛσTwkT {T′ = T′} σ T = begin 
    Tsub (Textₛ σ _) (Twk T)
  ≡⟨ fusion-Tsub-Tren T (Twkᵣ Tidᵣ) (Textₛ σ _) ⟩
    Tsub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′) T
  ≡⟨ sym (fusion-Tsub-Tsub T _ σ) ⟩
    Tsub σ (Tsub Tidₛ T)
  ≡⟨ cong (λ T → Tsub σ T) (TidₛT≡T T) ⟩
    Tsub σ T
  ∎

Tliftₛ∘Textₛ : ∀ l (τ* : TSub Δ []) (T′ : Type [] l) → Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′ ≡ (Textₛ τ* T′)
Tliftₛ∘Textₛ l τ* T′ = fun-ext₂ λ where
  _ here → refl
  _ (there x) →
    begin
      (Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′) _ (there x)
    ≡⟨ refl ⟩
      Tsub (Textₛ (λ z → `_) T′) (Tren (λ z x₂ → there x₂) (τ* _ x))
    ≡⟨ fusion-Tsub-Tren (τ* _ x)  (λ z x₂ → there x₂) (Textₛ (λ z → `_) T′) ⟩
      Tsub ((λ z x₂ → there x₂) ∘ᵣₛ Textₛ (λ z → `_) T′) (τ* _ x)
    ≡⟨ TidₛT≡T (τ* _ x) ⟩
      τ* _ x
    ≡⟨ refl ⟩
      Textₛ τ* T′ _ (there x)
    ∎

σ↑T[T′]≡TextₛσT′T : (σ* : TSub Δ []) (T′ : Type [] l) (T : Type (l ∷ Δ) l′)
  → Tsub (Tliftₛ σ* l) T [ T′ ]T ≡ Tsub (Textₛ σ* T′) T
σ↑T[T′]≡TextₛσT′T σ* T′ T =
  begin
    Tsub (Textₛ (λ z → `_) T′) (Tsub (Tliftₛ σ* _) T)
  ≡⟨ fusion-Tsub-Tsub T _ _ ⟩
    Tsub (Tliftₛ σ* _ ∘ₛₛ Textₛ (λ z → `_) T′) T
  ≡⟨ cong (λ τ* → Tsub τ* T) (fun-ext₂ aux) ⟩
    Tsub (Textₛ σ* T′) T
  ∎
  where
    aux : ∀ {l}{Δ}{σ* : TSub Δ []} {T′ : Type [] l} → (x : Level) (y : x ∈ (l ∷ Δ)) → (Tliftₛ σ* l ∘ₛₛ Textₛ (λ z → `_) T′) x y ≡ Textₛ σ* T′ x y
    aux _ here = refl
    aux {σ* = σ*}{T′ = T′} x (there y) = trans (fusion-Tsub-Tren (σ* x y) (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′)) (TidₛT≡T (σ* x y))


T[T′]T≡Tidₛ↑T[T′]T : ∀ (T : Type (l′ ∷ Δ) l) (T′ : Type Δ l′) → (T [ T′ ]T) ≡ (Tsub (Tliftₛ Tidₛ l′) T [ T′ ]T)
T[T′]T≡Tidₛ↑T[T′]T T T′ =
  begin
    (T [ T′ ]T)
  ≡⟨ sym (TidₛT≡T (T [ T′ ]T)) ⟩
    Tsub Tidₛ (T [ T′ ]T)
  ≡⟨ swap-Tsub-[] Tidₛ T T′ ⟩
    (Tsub (Tliftₛ Tidₛ _) T [ Tsub Tidₛ T′ ]T)
  ≡⟨ cong (λ T′ → Tsub (Tliftₛ Tidₛ _) T [ T′ ]T) (TidₛT≡T T′) ⟩
    (Tsub (Tliftₛ Tidₛ _) T [ T′ ]T)
  ∎

Text-sub-sub : ∀ {l′}{Δ₁}{Δ₂}
  → (σ* : TSub Δ₁ Δ₂)
  → (T′ : Type Δ₁ l′)
  → (x : Level)
  → (y : x ∈ (l′ ∷ Δ₁))
  → Textₛ σ* (Tsub σ* T′) x y ≡
      (Textₛ Tidₛ T′ ∘ₛₛ σ*) x y
Text-sub-sub σ* T′ x here = refl
Text-sub-sub σ* T′ x (there y) = refl


