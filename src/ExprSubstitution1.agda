{-# OPTIONS --allow-unsolved-metas #-}
module ExprSubstitution1 where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import Expressions

-- expr substitution

-- composition of renamings and substituions

_∘ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ₁ ∘ₛₛ σ₂) _ x = Tsub σ₂ (σ₁ _ x)

_∘ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ ∘ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_∘ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(ρ ∘ᵣₛ σ) _ x = σ _ (ρ _ x)

_∘ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ ∘ₛᵣ ρ) _ x = Tren ρ (σ _ x)

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

↑ρ-TwkT≡Twk-ρT : ∀ (T : Type Δ₁ l′) (ρ : TRen Δ₁ Δ₂) →
  Tren (Tliftᵣ ρ l) (Twk T) ≡ Twk (Tren ρ T) 
↑ρ-TwkT≡Twk-ρT {l = l} T ρ = 
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
   _ (there x) → sym (↑ρ-TwkT≡Twk-ρT (σ _ x) ρ)

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

σ↑-TwkT≡Twk-σT : ∀ {l} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l′) →
  Tsub (Tliftₛ σ _) (Twk {l = l} T) ≡ Twk (Tsub σ T)
σ↑-TwkT≡Twk-σT σ T = 
  begin 
    Tsub (Tliftₛ σ _) (Twk T) 
  ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Tliftₛ σ _) ⟩
    Tsub (σ ∘ₛᵣ λ _ → there) T
  ≡⟨ sym (assoc-ren-sub T σ (Twkᵣ Tidᵣ)) ⟩
    Tren (Twkᵣ Tidᵣ) (Tsub σ T)
  ∎


sub↑-dist-∘ₛₛ : ∀ l (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
  Tliftₛ (σ₁ ∘ₛₛ σ₂) _  ≡ (Tliftₛ σ₁ l ∘ₛₛ Tliftₛ σ₂ _)
sub↑-dist-∘ₛₛ l σ₁ σ₂ = fun-ext₂ λ where 
  _ here → refl
  l′ (there x) → begin 
        (Tliftₛ (σ₁ ∘ₛₛ σ₂) l) l′ (there x) 
      ≡⟨ sym (σ↑-TwkT≡Twk-σT {l = l} σ₂ (σ₁ l′ x)) ⟩
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
TidᵣT≡T {Δ = Δ} (`∀α l , T) rewrite TliftᵣTidᵣ≡Tidᵣ Δ l = cong (`∀α l ,_) (TidᵣT≡T T)
TidᵣT≡T `ℕ = refl

ρ[T]≡[ρT]ρ↑ : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) →
  Textₛ Tidₛ T ∘ₛᵣ ρ ≡ (Tliftᵣ ρ _) ∘ᵣₛ Textₛ Tidₛ (Tren ρ T)
ρ[T]≡[ρT]ρ↑ T ρ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

ρT[T′]≡ρT[ρ↑T′] : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tren ρ (T [ T′ ]T) ≡ Tren (Tliftᵣ ρ _) T [ Tren ρ T′ ]T 
ρT[T′]≡ρT[ρ↑T′] ρ T T′ = begin 
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
TidₛT≡T {Δ = Δ} (`∀α l , T) rewrite TliftₛTidₛ≡Tidₛ Δ l = cong (`∀α l ,_) (TidₛT≡T T)
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

σT[T′]≡σ↑T[σT'] : ∀ (σ : TSub Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tsub σ (T [ T′ ]T) ≡ (Tsub (Tliftₛ σ _) T) [ Tsub σ T′ ]T  
σT[T′]≡σ↑T[σT'] σ T T′ = 
  begin 
    Tsub σ (T [ T′ ]T) 
  ≡⟨ assoc-sub-sub T (Textₛ Tidₛ T′) σ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛₛ σ) T
  ≡⟨ cong (λ σ → Tsub σ T) (σ[T]≡[σT]σ↑ T′ σ) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ (Tsub σ T′)) T
  ≡⟨ sym (assoc-sub-sub T (Tliftₛ σ _) (Textₛ Tidₛ (Tsub σ T′))) ⟩
    (Tsub (Tliftₛ σ _) T) [ Tsub σ T′ ]T
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

-- expression renamings

ERen : TRen Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ERen {Δ₁}{Δ₂} ρ* Γ₁ Γ₂ = ∀ {l} {T : Type Δ₁ l} → inn T Γ₁ → inn (Tren ρ* T) Γ₂

Eidᵣ : ERen Tidᵣ Γ Γ 
Eidᵣ {T = T} x rewrite TidᵣT≡T T = x

Edropᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* (T ◁ Γ₁) Γ₂ → ERen ρ* Γ₁ Γ₂
Edropᵣ ρ* ρ x = ρ (there x)

Ewkᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* Γ₁ Γ₂ → ERen ρ* Γ₁ (T ◁ Γ₂) 
Ewkᵣ ρ* ρ x = there (ρ x) 

Eliftᵣ : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → ERen ρ* (T ◁ Γ₁) (Tren ρ* T ◁ Γ₂)
Eliftᵣ ρ here = here
Eliftᵣ ρ (there x) = there (ρ x)

Eliftᵣ-l : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → ERen (Tliftᵣ ρ* l) (l ◁* Γ₁) (l ◁* Γ₂)
Eliftᵣ-l {Γ₂ = Γ₂} {l = l} {ρ* = ρ*} ρ (tskip x) = subst id (cong (λ T → inn T (l ◁* Γ₂)) (sym (↑ρ-TwkT≡Twk-ρT _ ρ*))) (tskip (ρ x))

Eren : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tren ρ* T)
Eren ρ (# n) = # n
Eren ρ (` x) = ` ρ x
Eren ρ (ƛ e) = ƛ Eren (Eliftᵣ ρ) e
Eren ρ (e₁ · e₂) = Eren ρ e₁ · Eren ρ e₂
Eren ρ (Λ l ⇒ e) = Λ l ⇒ Eren (Eliftᵣ-l ρ) e
Eren {Δ₂ = Δ₂} {Γ₂ = Γ₂} {T = .(T [ T′ ]T)} {ρ* = ρ*} ρ (_∙_ {T = T} e T′) = 
  subst (Expr Δ₂ Γ₂) (sym (ρT[T′]≡ρT[ρ↑T′] ρ* T T′)) (Eren ρ e ∙ Tren ρ* T′)

Ewk : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) (T) 
Ewk {T = T} e = subst (λ T → Expr _ _ T) (TidᵣT≡T T) (Eren (Ewkᵣ Tidᵣ Eidᵣ) e)

Ewk-l : Expr Δ Γ T → Expr (l ∷ Δ) (l ◁* Γ) (Twk T)  
Ewk-l e = Eren tskip e

-- semantic renamings on expressions

ERen* : {ρ* : TRen Δ₁ Δ₂} (TRen* : TRen* ρ* η₁ η₂) → (ρ : ERen ρ* Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → Setω
ERen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ*} Tren* ρ γ₁ γ₂ = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ _ _ x)

ERen*-lift : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦e⟧ : ⟦ Tren ρ* T ⟧ η₂) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* Tren* (Eliftᵣ {T = T} ρ) (extend γ₁ (subst id (Tren*-preserves-semantics Tren* T) ⟦e⟧)) (extend γ₂ ⟦e⟧)
ERen*-lift {η₁ = η₁} {η₂ = η₂} {T = T} {ρ* = ρ*} ⟦e⟧ Tren* Eren* here 
  rewrite Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T = refl
ERen*-lift {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} ⟦e⟧ Tren* Eren* {T = T} (there x) = Eren* x

ERen*-lift-l : ∀ {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦α⟧ : Set l) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* (Tren*-lift ⟦α⟧ Tren*) (Eliftᵣ-l ρ) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₁) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₂)
ERen*-lift-l {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {l = l₁} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦α⟧ Tren* Eren* {l} (tskip {T = T} x) =
  let eq* = Eren* x in 
  let eq = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) (Twk T)) in 
  let eq' = sym (Tren*-preserves-semantics (wkᵣ∈Ren* η₁ ⟦α⟧) T) in 
  -- let eq'' = sym (Tren*-preserves-semantics {ρ* = ρ*} {η₂ = η₂} Tren* T) in
  let eq₁ = cong (λ T₁ → inn T₁ (l₁ ◁* Γ₂)) (sym (↑ρ-TwkT≡Twk-ρT T ρ*)) in
  begin 
    extend-tskip γ₂ _ (Tren (Tliftᵣ ρ* l₁) (Twk T)) (subst id eq₁ (tskip (ρ x)))
  ≡⟨ {!   !} ⟩
    subst id eq (extend-tskip γ₁ _ (Twk T) (tskip x))
  ≡⟨ {!   !} ⟩
    subst id eq (subst id eq' (γ₁ l T x))
  ∎

Eren*-preserves-semantics : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} →
  (Tren* : TRen* ρ* η₁ η₂) →
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  (e : Expr Δ₁ Γ₁ T) → 
  E⟦ Eren ρ e ⟧ η₂ γ₂ ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (E⟦ e ⟧ η₁ γ₁)
Eren*-preserves-semantics Tren* Eren* (# n) = refl
Eren*-preserves-semantics Tren* Eren* (` x) = Eren* x
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(T ⇒ T′)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (ƛ_ {T = T} {T′} e) = fun-ext λ ⟦e⟧ →
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ ρ} {γ₂ = extend γ₂ ⟦e⟧} Tren* (ERen*-lift {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦e⟧ Tren* Eren*) e  in
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = Tren*-preserves-semantics Tren* T in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren (Eliftᵣ ρ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ η₁ (extend γ₁ (subst id eq₁ ⟦e⟧)))
  ≡⟨ dist-subst (λ ⟦e⟧ → E⟦ e ⟧ η₁ (extend γ₁ ⟦e⟧)) eq₁ eq eq₂ ⟦e⟧ ⟩
    subst id eq (λ ⟦e⟧ → E⟦ e ⟧ η₁ (extend γ₁ ⟦e⟧)) ⟦e⟧
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_·_ {T = T} {T′ = T′} e₁ e₂) =
  let eq₁* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e₁ in
  let eq₂* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e₂ in
  let eq = sym (Tren*-preserves-semantics Tren* T′) in
  let eq₁ = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T) in
  let sub = subst id eq in 
  let sub₁ = subst id eq₁ in
  let sub₂ = subst id eq₂ in
  begin 
    E⟦ Eren ρ e₁ ⟧ η₂ γ₂ (E⟦ Eren ρ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
   (sub₁ (E⟦ e₁ ⟧ η₁ γ₁)) (sub₂ (E⟦ e₂ ⟧ η₁ γ₁))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ η₁ γ₁) eq₂ eq₁ eq (E⟦ e₂ ⟧ η₁ γ₁) ⟩
    sub (E⟦ e₁ ⟧ η₁ γ₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(`∀α l , T)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ-l ρ} {γ₁ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₁} {γ₂ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₂} 
            (Tren*-lift {η₁ = η₁} ⟦α⟧ Tren*) (ERen*-lift-l ⟦α⟧ Tren* Eren*) e in 
  let eq₁ = (λ { ⟦α⟧ → Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T }) in
  let eq = sym (dep-ext eq₁) in 
  let eq₂ = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T) in
  begin 
    E⟦ Eren (Eliftᵣ-l ρ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) ⟦α⟧
  ∎
Eren*-preserves-semantics {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_∙_ {l} {T = T} e T′) = 
  let eq* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e in 
  let eq*' = Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T′ in 
  let eq = (sym (ρT[T′]≡ρT[ρ↑T′] ρ* T T′)) in 
  let eq' = (sym (Tren*-preserves-semantics Tren* (T [ T′ ]T))) in 
  let eq'''' = λ α → Tren*-preserves-semantics {ρ* = Tliftᵣ ρ* l} {η₁ = α ∷ η₁} {η₂ = α ∷ η₂} (Tren*-lift α Tren*) T in
  let eq'' = (sym (dep-ext eq'''')) in
  let eq''' = sym (Tren*-preserves-semantics {ρ* = Tliftᵣ ρ* l} {η₁ = ⟦ Tren ρ* T′ ⟧ η₂ ∷ η₁} {η₂ = ⟦ Tren ρ* T′ ⟧ η₂ ∷ η₂} (Tren*-lift (⟦ Tren ρ* T′ ⟧ η₂) Tren*) T) in
  let eq₁ = (cong (λ T → ⟦ T ⟧ η₂) eq) in
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tren ρ* T′) (Tren (Tliftᵣ ρ* _) T)) in
  let eq₃ = sym (Tsingle-subst-preserves η₁ T′ T) in
  let eq₄ = cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym eq*') in
  let eq₅ = (cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym (Tren*-preserves-semantics Tren* T′))) in
  begin 
    E⟦ subst (Expr Δ₂ Γ₂) eq (Eren ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Eren ρ e ∙ Tren ρ* T′) ⟩
    subst id eq₁ (E⟦ (Eren ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂)
  ≡⟨⟩
    subst id eq₁ (subst id eq₂ (E⟦ (Eren ρ e) ⟧ η₂ γ₂ (⟦ Tren ρ* T′ ⟧ η₂)))
  ≡⟨ cong (λ e → subst id eq₁ (subst id eq₂ (e (⟦ Tren ρ* T′ ⟧ η₂)))) eq* ⟩
    subst id eq₁ (subst id eq₂ ((subst id eq'' (E⟦ e ⟧ η₁ γ₁)) (⟦ Tren ρ* T′ ⟧ η₂)))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂ x)) 
     (sym (dist-subst′′ (⟦ Tren ρ* T′ ⟧ η₂) (E⟦ e ⟧ η₁ γ₁) eq'' λ α → sym (eq'''' α))) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''' ((E⟦ e ⟧ η₁ γ₁) (⟦ Tren ρ* T′ ⟧ η₂))))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂  (subst id eq''' x))) 
     (dist-subst′′′ (⟦ Tren ρ* T′ ⟧ η₂) (⟦ T′ ⟧ η₁) (E⟦ e ⟧ η₁ γ₁) (Tren*-preserves-semantics Tren* T′) eq₅) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''' (subst id eq₄ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))))
  ≡⟨ dist-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)  
  ∎

--Goal
--E⟦
--subst (Expr Δ₂ Γ₂) (sym (ρT[T′]≡ρT[ρ↑T′] ρ* T T′))
--(Eren ρ e ∙ Tren ρ* T′)
--⟧
--η₂ γ₂
--≡
--subst id (sym (Tren*-preserves-semantics Tren* (T [ T′ ]T)))
--(E⟦ e ∙ T′ ⟧ η₁ γ₁ | ⟦ T [ T′ ]T ⟧ η₁
-- | Tsingle-subst-preserves η₁ T′ T)

-- expression substitutions

ESub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ESub {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ* Γ₁ Γ₂ = ∀ l {T : Type Δ₁ l} → inn T Γ₁ → Expr Δ₂ Γ₂ (Tsub σ* T)

Eidₛ : ESub Tidₛ Γ Γ
Eidₛ _ {T = T} rewrite TidₛT≡T T = `_

Ewkₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub σ* Γ₁ (T ◁ Γ₂)
Ewkₛ σ* σ _ {T = T} x = Ewk (σ _ x)

Edropₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* (T ◁ Γ₁) Γ₂ → ESub σ* Γ₁ Γ₂
Edropₛ σ* σ _ x = σ _ (there x)

Eliftₛ : ∀ {l} {T : Type Δ₁ l} (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub σ* (T ◁ Γ₁) ((Tsub σ* T) ◁ Γ₂)
Eliftₛ _ σ _ here = ` here
Eliftₛ _ σ _ (there x) = Ewk (σ _ x)

Eliftₛ-l : ∀ {l} → (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub (Tliftₛ σ* _) (l ◁* Γ₁) (l ◁* Γ₂)
Eliftₛ-l σ* σ _ (tskip {T = T} x) = subst (Expr _ _) (sym (σ↑-TwkT≡Twk-σT σ* T)) (Ewk-l (σ _ x))

Esub : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tsub σ* T)
Esub σ* σ (# n) = # n
Esub σ* σ (` x) = σ _ x
Esub σ* σ (ƛ e) = ƛ Esub σ* (Eliftₛ σ* σ) e
Esub σ* σ (e₁ · e₂) = Esub σ* σ e₁ · Esub σ* σ e₂
Esub σ* σ (Λ l ⇒ e) = Λ l ⇒ Esub (Tliftₛ σ* _) (Eliftₛ-l σ* σ) e
Esub σ* σ (_∙_ {T = T} e T′) = subst (Expr _ _) (sym (σT[T′]≡σ↑T[σT'] σ* T T′)) (Esub σ* σ e ∙ (Tsub σ* T′))

Eextₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → Expr Δ₂ Γ₂ (Tsub σ* T) → ESub σ* (T ◁ Γ₁) Γ₂
Eextₛ σ* σ e' _ here = e'
Eextₛ σ* σ e' _ (there x) = σ _ x

Eextₛ-l : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub (Textₛ σ* T) (l ◁* Γ₁) Γ₂
Eextₛ-l {Δ₂ = Δ₂} {Γ₂ = Γ₂} σ* σ _ (tskip {T = T} x) = subst (Expr Δ₂ Γ₂) (sym (σT≡TextₛσTwkT σ* T)) (σ _ x) 

_[_]E : Expr Δ (T₁ ◁ Γ) T₂ → Expr Δ Γ T₁ → Expr Δ Γ T₂
_[_]E {T₁ = T₁} {T₂ = T₂} e e′ = 
  subst (Expr _ _) (TidₛT≡T T₂) (Esub Tidₛ (Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T T₁)) e′)) e)

_[_]ET : Expr (l ∷ Δ) (l ◁* Γ) T → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)
e [ T ]ET = Esub (Textₛ Tidₛ T) (Eextₛ-l Tidₛ Eidₛ) e

sub0 : Expr Δ Γ (Tsub Tidₛ T₁) → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0 e′ = Eextₛ Tidₛ Eidₛ e′


sub0′ : Expr Δ Γ T₁ → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0′ e′ = Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T _)) e′)


-- general equality of expression substitutions

_~_ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → Set
_~_ {Δ₁ = Δ₁} {Γ₁ = Γ₁} σ₁ σ₂ = ∀ l {T : Type Δ₁ l} → (x : inn T Γ₁) → σ₁ l x ≡ σ₂ l x

~-lift : ∀ {l} {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → Eliftₛ {T = T} σ* σ₁ ~ Eliftₛ σ* σ₂
~-lift σ₁ σ₂ σ₁~σ₂ l here = refl
~-lift σ₁ σ₂ σ₁~σ₂ l (there x) = cong Ewk (σ₁~σ₂ l x)

~-lift* : ∀ {l : Level} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (Eliftₛ-l {l = l} σ* σ₁) ~ Eliftₛ-l σ* σ₂
~-lift* σ₁ σ₂ σ₁~σ₂ l (tskip x) rewrite σ₁~σ₂ l x = refl


Esub~ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (e : Expr Δ₁ Γ₁ T) → Esub σ* σ₁ e ≡ Esub σ* σ₂ e
Esub~ σ₁ σ₂ σ₁~σ₂ (# n) = refl
Esub~ σ₁ σ₂ σ₁~σ₂ (` x) = σ₁~σ₂ _ x
Esub~ σ₁ σ₂ σ₁~σ₂ (ƛ e) = cong ƛ_ (Esub~ _ _ (~-lift σ₁ σ₂ σ₁~σ₂) e)
Esub~ σ₁ σ₂ σ₁~σ₂ (e · e₁) = cong₂ _·_ (Esub~ σ₁ σ₂ σ₁~σ₂ e) (Esub~ σ₁ σ₂ σ₁~σ₂ e₁)
Esub~ σ₁ σ₂ σ₁~σ₂ (Λ l ⇒ e) = cong (Λ l ⇒_) (Esub~ _ _ (~-lift* {l = l} σ₁ σ₂ σ₁~σ₂) e)
Esub~ σ₁ σ₂ σ₁~σ₂ (e ∙ T′) rewrite Esub~ σ₁ σ₂ σ₁~σ₂ e = refl

--- want to prove
--- Goal: Esub σ* (Eextₛ σ* σ e′) e
---     ≡ (Esub σ* (Eliftₛ σ* σ) e) [ e′ ]E
---
--- at the level of substitutions
---
---     (Eextₛ σ* σ e′) ~  (Eliftₛ σ* σ) >>S sub0 e′

-- composition of expression substitutions

_>>S_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ₁* Γ₁ Γ₂ → ESub σ₂* Γ₂ Γ₃ → ESub (σ₁* ∘ₛₛ σ₂*) Γ₁ Γ₃
_>>S_ {Δ₃ = Δ₃}{σ₁* = σ₁*}{σ₂* = σ₂*}{Γ₃ = Γ₃} σ₁ σ₂ l {T} x
  = subst (Expr Δ₃ Γ₃) (assoc-sub-sub T  σ₁* σ₂*) (Esub _ σ₂ (σ₁ l x))

TSub-id-right : ∀ (σ* : TSub Δ₁ Δ₂) → (σ* ∘ₛₛ Tidₛ) ≡ σ*
TSub-id-right {Δ₁ = Δ₁} σ* = fun-ext₂ aux
  where
    aux : (l : Level) (x : l ∈ Δ₁) → (σ* ∘ₛₛ Tidₛ) l x ≡ σ* l x
    aux l x = TidₛT≡T (σ* l x)

TSub-id-left :  ∀ (σ* : TSub Δ₁ Δ₂) → (Tidₛ ∘ₛₛ σ*) ≡ σ*
TSub-id-left {Δ₁} σ* = fun-ext₂ aux
  where
    aux : (l : Level) (x : l ∈ Δ₁) → (Tidₛ ∘ₛₛ σ*) l x ≡ σ* l x
    aux l x = refl


module using-sub0′ where

  Eext-Elift[]~-type : Set
  Eext-Elift[]~-type = ∀ {l}{Δ₁}{Δ₂}
    → {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    → (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
    → let r = Eliftₛ {T = T} σ* σ >>S sub0′ e′ in
      let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
       subᵣ r ~ Eextₛ {T = T} σ* σ e′
    

  sub0-e′-wk-e≡e : ∀ {Δ}{Γ}{l′}{T′ : Type Δ l′}{l}{T : Type Δ l}
    → (e′ : Expr Δ Γ T′) (e : Expr Δ Γ T)
    → Esub Tidₛ (sub0′ e′) (Ewk e) ≡ subst (Expr Δ Γ) (sym (TidₛT≡T T)) e
  sub0-e′-wk-e≡e e′ (# n) = refl
  sub0-e′-wk-e≡e e′ (` x) = {!!}
  sub0-e′-wk-e≡e e′ (ƛ e) = {!!}
  sub0-e′-wk-e≡e e′ (e · e₁) = {!!}
  sub0-e′-wk-e≡e e′ (Λ l ⇒ e) = {!!}
  sub0-e′-wk-e≡e e′ (e ∙ T′) = {!!}


  Eext-Elift[]~ : Eext-Elift[]~-type
  Eext-Elift[]~ {.l₁} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ {.T} here =
    let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
    let sub₂ = subst (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*)) in
    let sub₃ = subst (Expr Δ₂ Γ₂) (trans (TidₛT≡T (Tsub σ* T)) (cong (λ τ* → Tsub τ* T) (sym (TSub-id-right σ*)))) in
    let sub₄ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
    begin
      sub₁ (Eliftₛ σ* σ >>S sub0′ e′) l₁ here
    ≡⟨ dist-subst' (λ f → {!f l₁ !}) (λ f → f l₁ here) (TSub-id-right σ*) (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*)) (Eliftₛ {T = T} σ* σ >>S sub0′ e′)  ⟩
      sub₂ ((Eliftₛ {T = {!T!}} σ* σ >>S sub0′ e′) l₁ here)
    ≡⟨⟩
      sub₂ (sub₃ (Esub _ (sub0′ e′) (Eliftₛ {T = T} σ* σ  l₁ here)))
    ≡⟨⟩
      sub₂ (sub₃ (sub₄ e′))
    ≡⟨ elim-subst₃ (Expr Δ₂ Γ₂) 
                   (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*))
                   (trans (TidₛT≡T (Tsub σ* T)) (cong (λ τ* → Tsub τ* T) (sym (TSub-id-right σ*))))
                   (sym (TidₛT≡T (Tsub σ* T))) e′ ⟩
      e′
    ∎
{-
Goal: subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂)
            (TSub-id-right σ*)
            (Eliftₛ σ* σ >>S sub0′ e′) l₁ here
      ≡
      subst (Expr Δ₂ Γ₂)
            (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*))
            ((Eliftₛ σ* σ >>S sub0′ e′) l₁ here)
-}
    -- (subst K₁ ≡₁ F) x y ≈ subst K₂ ≡₂ (F x y)
    -- for dist-subst'
    -- f = λ substF → substF x y

  Eext-Elift[]~ {l₂} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ {T₂} (there x) = {!!}


Eext-Elift[]~-type : Set
Eext-Elift[]~-type = ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
  → let r = Eliftₛ {T = T} σ* σ >>S sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
    let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
    Eextₛ {T = T} σ* σ e′ ~ subᵣ r


sub0-e′-wk-e≡e : ∀ {Δ}{Γ}{l′}{T′ : Type Δ l′}{l}{T : Type Δ l} → (e′ : Expr Δ Γ (Tsub Tidₛ T′)) (e : Expr Δ Γ T) → Esub Tidₛ (sub0 e′) (Ewk e) ≡ subst (Expr Δ Γ) (sym (TidₛT≡T T)) e
sub0-e′-wk-e≡e e′ (# n) = refl
sub0-e′-wk-e≡e e′ (` x) = {!!}
sub0-e′-wk-e≡e e′ (ƛ e) = {!!}
sub0-e′-wk-e≡e e′ (e · e₁) = {!!}
sub0-e′-wk-e≡e e′ (Λ l ⇒ e) = {!!}
sub0-e′-wk-e≡e e′ (e ∙ T′) = {!!}


Eext-Elift[]~ : Eext-Elift[]~-type
Eext-Elift[]~ {.l₁} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ {.T} here =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (TSub-id-right σ*)) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T  σ* Tidₛ) in
  begin
    e′
      ≡⟨ sym (elim-subst₃ (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (TSub-id-right σ*)) (assoc-sub-sub T  σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T))) e′) ⟩
    sub₁′ (sub₃ (sub₂ e′))
      ≡⟨ refl ⟩
    sub₁′ (sub₃ (Esub _ (sub0 (sub₂ e′)) (` here)))
      ≡⟨ refl ⟩
    sub₁′ (sub₃ (Esub _ (sub0 (sub₂ e′)) ((Eliftₛ σ* σ) l₁ here)))
      ≡⟨ refl ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ here)
      ≡⟨ sym (dist-subst' {F = (λ a → ESub a (T ◁ Γ₁) Γ₂)} {G = Expr Δ₂ Γ₂} {!!} (λ f → f l₁ here) (TSub-id-right σ*) (cong (λ σ*₁ → Tsub σ*₁ T) (TSub-id-right σ*)) (Eliftₛ σ* σ >>S
       sub0 (subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) e′))) ⟩
    sub₁ (Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ here 
  ∎
Eext-Elift[]~ {l} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ {T₁} (there x) =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*)) in
  let sub₁″ = subst (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁)) (TSub-id-right σ*) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T₁ σ* Tidₛ) in
  sym $ begin
    sub₁ (Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ (there x)
      ≡⟨ {!sub0 (sub₂ e′)!} ⟩
    sub₁ (Eliftₛ σ* σ >>S sub0 {!e′!}) l₁ (there x)
      ≡⟨ {!sub0 e′!} ⟩
    sub₁″ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ (there x))
      ≡⟨ sym (subst-cong (Expr Δ₂ Γ₂) (λ τ* → Tsub τ* T₁) (TSub-id-right σ*) ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ (there x))) ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ (there x))
      ≡⟨ refl ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 e′) l₁ (there x))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub _ (sub0 e′) (Eliftₛ σ* σ l₁ (there x))))
      ≡⟨ cong sub₁′ (cong sub₃ (sub0-e′-wk-e≡e {l′ = l} e′ (σ l₁ x))) ⟩
    sub₁′ (sub₃ ((subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T _)) (σ l₁ x))))
      ≡⟨ elim-subst₃ (Expr Δ₂ Γ₂)
           (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*))
           (assoc-sub-sub T₁ σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T₁))) (σ l₁ x)
       ⟩
    σ l₁ x   -- : Expr Δ₂ Γ₂ (Tsub σ* T₁)
  ∎

-- Eext-Elift[]~ : ∀ {σ*  TSub Δ₁ Δ₂} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
--   → Eextₛ σ* σ e′ ~ (Eliftₛ σ* σ >>S ((Eextₛ Tidₛ Eidₛ e′)))
-- Eext-Elift[]~ σ e′ = ?