{-# OPTIONS --allow-unsolved-metas #-}
module ExprSubstProperties where

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
open import ExprSubstitution

-- single substitution dissected

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



Eext-Elift[]~-type : Set
Eext-Elift[]~-type =
  ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
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
      ≡⟨ sym (elim-subst₃ (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*)) (assoc-sub-sub T  σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T))) e′) ⟩
    sub₁′ (sub₃ (sub₂ e′))
      ≡⟨ refl ⟩
    sub₁′ (sub₃ (Esub _ (sub0 (sub₂ e′)) (` here)))
      ≡⟨ refl ⟩
    sub₁′ (sub₃ (Esub _ (sub0 (sub₂ e′)) ((Eliftₛ σ* σ) l₁ here)))
      ≡⟨ refl ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ here)
      ≡⟨ sym (dist-subst' {F = (λ a → ESub a (T ◁ Γ₁) Γ₂)} {G = Expr Δ₂ Γ₂}
                          (λ τ* → Tsub τ* T)
                          (λ f → f l₁ here)
                          (TSub-id-right σ*)
                          (cong (λ σ*₁ → Tsub σ*₁ T) (TSub-id-right σ*))
                          (Eliftₛ σ* σ >>S sub0 (subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) e′)))
       ⟩
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
      ≡⟨ dist-subst' {F = (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂)} {G = (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁))} id (λ τ → τ l₁ (there x)) (TSub-id-right σ*) (TSub-id-right σ*) (Eliftₛ σ* σ >>S sub0 (sub₂ e′)) ⟩
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
    σ l₁ x
  ∎
