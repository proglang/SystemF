module TypeSubstProperties where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
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
open import SetOmega
open import TypeSubstitution

-- composition of type substitutions

-- composition of renamings and substituions

_∘ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ ∘ₛᵣ ρ) _ x = Tren ρ (σ _ x)

_∘ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(ρ ∘ᵣₛ σ) _ x = σ _ (ρ _ x)

_∘ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ₁ ∘ₛₛ σ₂) _ x = Tsub σ₂ (σ₁ _ x)

_∘ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ ∘ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

-- interaction of renamings and substituions

sub↑-dist-∘ᵣₛ : ∀ l (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
  Tliftₛ (ρ ∘ᵣₛ σ) _ ≡ Tliftᵣ ρ l ∘ᵣₛ Tliftₛ σ _ 
sub↑-dist-∘ᵣₛ l ρ σ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

mutual 
  assoc-sub↑-ren↑ : ∀ (T : Type (l ∷ Δ₁) l′) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ _) (Tren (Tliftᵣ ρ _) T) ≡ Tsub (Tliftₛ (ρ ∘ᵣₛ σ) _) T
  assoc-sub↑-ren↑ T ρ σ = begin
      Tsub (Tliftₛ σ _) (Tren (Tliftᵣ ρ _) T) 
    ≡⟨ assoc-sub-ren T (Tliftᵣ ρ _) (Tliftₛ σ _) ⟩
      Tsub (Tliftᵣ ρ _ ∘ᵣₛ Tliftₛ σ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ᵣₛ _ ρ σ)) ⟩
      Tsub (Tliftₛ (ρ ∘ᵣₛ σ) _) T
    ∎

  assoc-sub-ren : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub σ (Tren ρ T) ≡ Tsub (ρ ∘ᵣₛ σ) T
  assoc-sub-ren (` x) ρ σ = refl
  assoc-sub-ren (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (assoc-sub-ren T₁ ρ σ) (assoc-sub-ren T₂ ρ σ)
  assoc-sub-ren (`∀α l , T) ρ σ = cong (`∀α l ,_) (assoc-sub↑-ren↑ T ρ σ)
  assoc-sub-ren `ℕ ρ σ = refl

ren↑-dist-∘ᵣᵣ : ∀ l (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
  Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _ ≡ ((Tliftᵣ ρ₁ l) ∘ᵣᵣ (Tliftᵣ ρ₂ _)) 
ren↑-dist-∘ᵣᵣ l ρ₁ ρ₂ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

mutual 
  assoc-ren↑-ren↑ : ∀ (T : Type (l ∷ Δ₁) l′) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ₂ _) (Tren (Tliftᵣ ρ₁ _) T) ≡ Tren (Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _) T
  assoc-ren↑-ren↑ {l = l} T ρ₁ ρ₂ =
      Tren (Tliftᵣ ρ₂ _) (Tren (Tliftᵣ ρ₁ _) T) 
    ≡⟨ assoc-ren-ren T (Tliftᵣ ρ₁ _) (Tliftᵣ ρ₂ _) ⟩
      Tren (Tliftᵣ ρ₁ _ ∘ᵣᵣ Tliftᵣ ρ₂ _) T
    ≡⟨ cong (λ ρ → Tren ρ T) (sym (ren↑-dist-∘ᵣᵣ l ρ₁ ρ₂))  ⟩
      Tren (Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _) T
    ∎

  assoc-ren-ren : ∀ (T : Type Δ₁ l) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren ρ₂ (Tren ρ₁ T) ≡ Tren (ρ₁ ∘ᵣᵣ ρ₂) T
  assoc-ren-ren (` x) ρ₁ ρ₂ = refl
  assoc-ren-ren (T₁ ⇒ T₂) ρ₁ ρ₂ = cong₂ _⇒_ (assoc-ren-ren T₁ ρ₁ ρ₂) (assoc-ren-ren T₂ ρ₁ ρ₂)
  assoc-ren-ren (`∀α l , T) ρ₁ ρ₂ = cong (`∀α l ,_) (assoc-ren↑-ren↑ T ρ₁ ρ₂)
  assoc-ren-ren `ℕ ρ₁ ρ₂ = refl

swap-Tren-Twk : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type Δ₁ l′) →
  Tren (Tliftᵣ ρ l) (Twk T) ≡ Twk (Tren ρ T) 
swap-Tren-Twk {l = l} ρ T = 
  begin 
    Tren (Tliftᵣ ρ _) (Tren (Twkᵣ Tidᵣ) T)
  ≡⟨ assoc-ren-ren T (Twkᵣ Tidᵣ) (Tliftᵣ ρ _) ⟩
    Tren ((Twkᵣ Tidᵣ) ∘ᵣᵣ Tliftᵣ ρ _) T
  ≡⟨ sym (assoc-ren-ren T ρ (Twkᵣ Tidᵣ)) ⟩
    Tren (Twkᵣ Tidᵣ) (Tren ρ T)
  ∎

ren↑-dist-∘ₛᵣ : ∀ l (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
  Tliftₛ (σ ∘ₛᵣ ρ) l ≡ (Tliftₛ σ l ∘ₛᵣ Tliftᵣ ρ _)
ren↑-dist-∘ₛᵣ l σ ρ = fun-ext₂ λ where 
   _ here → refl
   _ (there x) → sym (swap-Tren-Twk ρ (σ _ x))

mutual 
  assoc-ren↑-sub↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ _) (Tsub (Tliftₛ σ _) T) ≡ Tsub (Tliftₛ (σ ∘ₛᵣ ρ) _) T
  assoc-ren↑-sub↑ {l = l} T σ ρ = begin 
      Tren (Tliftᵣ ρ _) (Tsub (Tliftₛ σ _) T)
    ≡⟨ assoc-ren-sub T (Tliftₛ σ _) (Tliftᵣ ρ _) ⟩
      Tsub (Tliftₛ σ _ ∘ₛᵣ Tliftᵣ ρ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (ren↑-dist-∘ₛᵣ l σ ρ)) ⟩
      Tsub (Tliftₛ (σ ∘ₛᵣ ρ) _) T
    ∎ 

  assoc-ren-sub : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren ρ (Tsub σ T) ≡ Tsub (σ ∘ₛᵣ ρ) T
  assoc-ren-sub (` x) ρ σ = refl
  assoc-ren-sub (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (assoc-ren-sub T₁ ρ σ) (assoc-ren-sub T₂ ρ σ)
  assoc-ren-sub (`∀α l , T) ρ σ = cong (`∀α l ,_) (assoc-ren↑-sub↑ T ρ σ)
  assoc-ren-sub `ℕ ρ σ = refl

swap-Tsub-Twk : ∀ {l} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l′) →
  Tsub (Tliftₛ σ _) (Twk {l = l} T) ≡ Twk (Tsub σ T)
swap-Tsub-Twk σ T = 
  begin 
    Tsub (Tliftₛ σ _) (Twk T) 
  ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Tliftₛ σ _) ⟩
    Tsub (σ ∘ₛᵣ λ _ → there) T
  ≡⟨ sym (assoc-ren-sub T σ (Twkᵣ Tidᵣ)) ⟩
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
  assoc-sub↑-sub↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ₂ _) (Tsub (Tliftₛ σ₁ _) T) ≡ Tsub (Tliftₛ (σ₁ ∘ₛₛ σ₂) _) T
  assoc-sub↑-sub↑ {l = l} T σ₁ σ₂ = begin 
      Tsub (Tliftₛ σ₂ _) (Tsub (Tliftₛ σ₁ _) T)
    ≡⟨ assoc-sub-sub T (Tliftₛ σ₁ _) (Tliftₛ σ₂ _) ⟩
      Tsub (Tliftₛ σ₁ _ ∘ₛₛ Tliftₛ σ₂ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ l σ₁ σ₂)) ⟩
      Tsub (Tliftₛ (σ₁ ∘ₛₛ σ₂) _) T
    ∎ 

  assoc-sub-sub : ∀ (T : Type Δ₁ l) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub σ₂ (Tsub σ₁ T) ≡ Tsub (σ₁ ∘ₛₛ σ₂) T
  assoc-sub-sub (` x) σ₁ σ₂ = refl
  assoc-sub-sub (T₁ ⇒ T₂) σ₁ σ₂ = cong₂ _⇒_ (assoc-sub-sub T₁ σ₁ σ₂) (assoc-sub-sub T₂ σ₁ σ₂)
  assoc-sub-sub (`∀α l , T) σ₁ σ₂ = cong (`∀α l ,_) (assoc-sub↑-sub↑ T σ₁ σ₂)
  assoc-sub-sub `ℕ σ₁ σ₂ = refl

TliftᵣTidᵣ≡Tidᵣ : ∀ Δ l →
  (Tliftᵣ {Δ₁ = Δ} Tidᵣ l) ≡ Tidᵣ
TliftᵣTidᵣ≡Tidᵣ _ _ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → refl

TidᵣT≡T : ∀ (T : Type Δ l) → Tren Tidᵣ T ≡ T
TidᵣT≡T (` x) = refl
TidᵣT≡T (T₁ ⇒ T₂) = cong₂ _⇒_ (TidᵣT≡T T₁) (TidᵣT≡T T₂)
TidᵣT≡T {Δ = Δ} (`∀α l , T) = cong (`∀α l ,_) (trans (cong (λ ρ → Tren ρ T) (TliftᵣTidᵣ≡Tidᵣ Δ l)) (TidᵣT≡T T))
TidᵣT≡T `ℕ = refl

∘ᵣₛ-neutralˡ : ∀ (σ : TSub Δ₁ Δ₂) → Tidᵣ ∘ᵣₛ σ ≡ σ
∘ᵣₛ-neutralˡ σ = refl

∘ₛᵣ-neutralˡ : ∀ (σ : TSub Δ₁ Δ₂) → σ ∘ₛᵣ Tidᵣ ≡ σ
∘ₛᵣ-neutralˡ σ = fun-ext λ l → fun-ext λ x → TidᵣT≡T (σ l x)

ρ[T]≡[ρT]ρ↑ : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) →
  Textₛ Tidₛ T ∘ₛᵣ ρ ≡ (Tliftᵣ ρ _) ∘ᵣₛ Textₛ Tidₛ (Tren ρ T)
ρ[T]≡[ρT]ρ↑ T ρ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

swap-Tren-[] : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tren ρ (T [ T′ ]T) ≡ Tren (Tliftᵣ ρ _) T [ Tren ρ T′ ]T 
swap-Tren-[] ρ T T′ = begin 
    Tren ρ (T [ T′ ]T)
  ≡⟨ assoc-ren-sub T (Textₛ Tidₛ T′) ρ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛᵣ ρ) T
  ≡⟨ cong (λ σ → Tsub σ T) (ρ[T]≡[ρT]ρ↑ T′ ρ) ⟩
    Tsub ((Tliftᵣ ρ _) ∘ᵣₛ (Textₛ Tidₛ (Tren ρ T′))) T
  ≡⟨ sym (assoc-sub-ren T (Tliftᵣ ρ _) (Textₛ Tidₛ (Tren ρ T′))) ⟩
    Tsub (Textₛ Tidₛ (Tren ρ T′)) (Tren (Tliftᵣ ρ _) T)
  ∎

TliftₛTidₛ≡Tidₛ : ∀ Δ l →                         
  (Tliftₛ {Δ₁ = Δ} Tidₛ l) ≡ Tidₛ
TliftₛTidₛ≡Tidₛ _ _ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → refl             

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
      ≡⟨ sym (assoc-sub-ren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ (Tsub σ T))) ⟩
        Tsub (Textₛ Tidₛ (Tsub σ T)) (Twk (σ _ x))
      ∎

swap-Tsub-[] : ∀ (σ : TSub Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tsub σ (T [ T′ ]T) ≡ (Tsub (Tliftₛ σ _) T) [ Tsub σ T′ ]T  
swap-Tsub-[] σ T T′ = 
  begin 
    Tsub σ (T [ T′ ]T) 
  ≡⟨ assoc-sub-sub T (Textₛ Tidₛ T′) σ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛₛ σ) T
  ≡⟨ cong (λ σ → Tsub σ T) (σ[T]≡[σT]σ↑ T′ σ) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ (Tsub σ T′)) T
  ≡⟨ sym (assoc-sub-sub T (Tliftₛ σ _) (Textₛ Tidₛ (Tsub σ T′))) ⟩
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
  ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Textₛ σ _) ⟩
    Tsub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′) T
  ≡⟨ sym (assoc-sub-sub T _ σ) ⟩
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
    ≡⟨ assoc-sub-ren (τ* _ x)  (λ z x₂ → there x₂) (Textₛ (λ z → `_) T′) ⟩
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
  ≡⟨ assoc-sub-sub T _ _ ⟩
    Tsub (Tliftₛ σ* _ ∘ₛₛ Textₛ (λ z → `_) T′) T
  ≡⟨ cong (λ τ* → Tsub τ* T) (fun-ext₂ aux) ⟩
    Tsub (Textₛ σ* T′) T
  ∎
  where
    aux : ∀ {l}{Δ}{σ* : TSub Δ []} {T′ : Type [] l} → (x : Level) (y : x ∈ (l ∷ Δ)) → (Tliftₛ σ* l ∘ₛₛ Textₛ (λ z → `_) T′) x y ≡ Textₛ σ* T′ x y
    aux _ here = refl
    aux {σ* = σ*}{T′ = T′} x (there y) = trans (assoc-sub-ren (σ* x y) (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′)) (TidₛT≡T (σ* x y))


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


-- the action of renaming on semantic environments

TRen* : (ρ* : TRen Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
TRen* {Δ₁} ρ* η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ* _ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → TRen* (Twkᵣ {Δ₁ = Δ}{l = l} Tidᵣ) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

Tren*-id : (η : Env* Δ) → TRen* (λ _ x → x) η η

Tren*-id η x = refl

Tren*-pop : (ρ* : TRen (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → 
  TRen* ρ* (α ∷ η₁) η₂ → TRen* (λ _ x → ρ* _ (there x)) η₁ η₂
Tren*-pop ρ* α η₁ η₂ Tren* x = Tren* (there x)

Tren*-lift : ∀ {ρ* : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → TRen* ρ* η₁ η₂ → TRen* (Tliftᵣ ρ* _) (α ∷ η₁) (α ∷ η₂)
Tren*-lift α Tren* here = refl
Tren*-lift α Tren* (there x) = Tren* x

Tren*-preserves-semantics : ∀ {ρ* : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (Tren* : TRen* ρ* η₁ η₂) → (T : Type Δ₁ l) →  ⟦ Tren ρ* T ⟧ η₂ ≡ ⟦ T ⟧ η₁
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (` x) = Tren* x
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (T₁ ⇒ T₂) = cong₂ (λ A₁ A₂ → A₁ → A₂) (Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* T₁) (Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* T₂)
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (`∀α l , T) = dep-ext λ where 
  α → Tren*-preserves-semantics{ρ* = Tliftᵣ ρ* _}{α ∷ η₁}{α ∷ η₂} (Tren*-lift {ρ* = ρ*} α Tren*) T
Tren*-preserves-semantics Tren* `ℕ = refl


-- the action of substitution on semantic environments

subst-to-env* : TSub Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
subst-to-env* {[]} σ* η₂ = []
subst-to-env* {x ∷ Δ₁} σ* η₂ = ⟦ σ* _ here ⟧ η₂ ∷ subst-to-env* (Tdropₛ σ*) η₂

subst-var-preserves : (x  : l ∈ Δ₁) (σ*  : TSub Δ₁ Δ₂) (η₂ : Env* Δ₂) → ⟦ σ* _ x ⟧ η₂ ≡ apply-env (subst-to-env* σ* η₂) x
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
  subst-var-preserves x σ* η₂
subst-preserves {η₂ = η₂} σ* (T₁ ⇒ T₂) =
  cong₂ (λ A B → A → B) (subst-preserves{η₂ = η₂} σ* T₁) (subst-preserves{η₂ = η₂} σ* T₂)
subst-preserves {η₂ = η₂} σ* (`∀α l , T) =
  dep-ext (λ ⟦α⟧ →
    trans (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ* _) T)
          (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ* ⟦α⟧ η₂)))
subst-preserves σ* `ℕ = refl
 
Tsingle-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′) → 
  ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
Tsingle-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (Textₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

subst-to-env*-comp : (σ* : TSub Δ₁ Δ₂) → (τ* : TSub Δ₂ Δ₃) → (η : Env* Δ₃) → subst-to-env* σ* (subst-to-env* τ* η) ≡ω subst-to-env* (σ* ∘ₛₛ τ*) η
subst-to-env*-comp {Δ₁ = []} σ* τ* η = refl
subst-to-env*-comp {Δ₁ = l ∷ Δ₁} σ* τ* η = conglωω _∷_ (sym (subst-preserves τ* (σ* l here))) (subst-to-env*-comp (Tdropₛ σ*) τ* η)

