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
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution

-- single substitution dissected

sub0 : Expr Δ Γ (Tsub Tidₛ T₁) → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0 e′ = Eextₛ Tidₛ Eidₛ e′

sub0′ : Expr Δ Γ T₁ → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0′ e′ = Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T _)) e′)


-- general equality of expression substitutions

_~_ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → Set
_~_ {Δ₁ = Δ₁} {Γ₁ = Γ₁} σ₁ σ₂ = ∀ l (T : Type Δ₁ l) → (x : inn T Γ₁) → σ₁ l T x ≡ σ₂ l T x

~-lift : ∀ {l} {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → Eliftₛ {T = T} σ* σ₁ ~ Eliftₛ σ* σ₂
~-lift σ₁ σ₂ σ₁~σ₂ l T here = refl
~-lift σ₁ σ₂ σ₁~σ₂ l T (there x) = cong Ewk (σ₁~σ₂ l T x)

~-lift* : ∀ {l : Level} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (Eliftₛ-l {l = l} σ* σ₁) ~ Eliftₛ-l σ* σ₂
~-lift* σ₁ σ₂ σ₁~σ₂ l _ (tskip x) rewrite σ₁~σ₂ l _ x = refl


Esub~ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (e : Expr Δ₁ Γ₁ T) → Esub σ* σ₁ e ≡ Esub σ* σ₂ e
Esub~ σ₁ σ₂ σ₁~σ₂ (# n) = refl
Esub~ σ₁ σ₂ σ₁~σ₂ (` x) = σ₁~σ₂ _ _ x
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

---- specialized ----
subst-split : ∀ {Δ}
  → {ℓ : Level}
  → (F : {l : Level} (t : Type Δ l) → Set ℓ)
  → (f : ∀ {t₁ : Type Δ l₁}{t₂ : Type Δ l₂} → F (t₁ ⇒ t₂) → F t₁ → F t₂)
  → {t₁ t₁′ : Type Δ l₁}{t₂ t₂′ : Type Δ l₂}
  → (eq : (t₁ ⇒ t₂)  ≡ (t₁′ ⇒ t₂′)) (eq₁ : t₁ ≡ t₁′) (eq₂ : t₂ ≡ t₂′)
  → (x₁ : F (t₁ ⇒ t₂)) (x₂ : F t₁)
  → subst F eq₂ (f x₁ x₂) ≡ f (subst F eq x₁) (subst F eq₁ x₂)
subst-split F f refl refl refl x₁ x₂ = refl


-- composition of expression substitutions

_>>S_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ₁* Γ₁ Γ₂ → ESub σ₂* Γ₂ Γ₃ → ESub (σ₁* ∘ₛₛ σ₂*) Γ₁ Γ₃
_>>S_ {Δ₃ = Δ₃}{σ₁* = σ₁*}{σ₂* = σ₂*}{Γ₃ = Γ₃} σ₁ σ₂ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-sub-sub T  σ₁* σ₂*) (Esub _ σ₂ (σ₁ l _ x))

-- ((l₁ : Level) {T = T₁ : Type Δ₁ l₁} →
--        inn T₁ (_T_480 (σ₁ = σ₁) (σ₂ = σ₂) ◁ Γ₁) →
--        Expr Δ₃ (Tsub (σ₁* ∘ₛₛ σ₂*) (_T_480 (σ₁ = σ₁) (σ₂ = σ₂)) ◁ Γ₃)
--        (Tsub (σ₁* ∘ₛₛ σ₂*) T₁))
--       ≡
--       ((l₁ : Level) {T = T₁ : Type Δ₁ l₁} →
--        inn T₁ (T ◁ Γ₁) →
--        Expr Δ₃ (Tsub σ₂* (Tsub σ₁* T) ◁ Γ₃) (Tsub (σ₁* ∘ₛₛ σ₂*) T₁))

Eassoc-sub-sub : 
    {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → (e : Expr Δ₁ Γ₁ T)
  → (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃)
  → let lhs = Esub σ₂* σ₂ (Esub σ₁* σ₁ e) in
    let rhs = Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂) e  in
    subst (Expr Δ₃ Γ₃) (assoc-sub-sub T σ₁* σ₂*) lhs ≡ rhs
  
Eassoc-sub↑-sub↑ :
    {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → {T′ : Type Δ₁ l′}
  → (e : Expr Δ₁ (T′ ◁  Γ₁) T)
  → (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃)
  → let lhs = Esub σ₂* (Eliftₛ {T = Tsub σ₁* T′} σ₂* σ₂) (Esub σ₁* (Eliftₛ σ₁* σ₁) e) in
    let rhs = Esub (σ₁* ∘ₛₛ σ₂*) (Eliftₛ {T = T′} (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂)) e  in
    subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) (subst (Expr Δ₃ _) (assoc-sub-sub T σ₁* σ₂*) lhs) ≡ rhs

Esub↑-dist-∘ₛₛ : {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃) 
  → Eliftₛ {T = T} σ₁* σ₁ >>S Eliftₛ σ₂* σ₂ ≡ 
    subst ((λ T → ESub _ _ (T ◁ Γ₃))) (sym (assoc-sub-sub T σ₁* σ₂*)) (Eliftₛ {T = T} (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂))
Esub↑-dist-∘ₛₛ {σ₁* = σ₁*} {σ₂* = σ₂*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} T σ₁ σ₂ = fun-ext λ l → fun-ext λ T₁ → fun-ext λ x → aux l T₁ x
  where aux : ∀ l T₁ x → (Eliftₛ σ₁* σ₁ >>S Eliftₛ σ₂* σ₂) l T₁ x ≡ subst (λ T₂ → ESub (σ₁* ∘ₛₛ σ₂*) (T ◁ Γ₁) (T₂ ◁ Γ₃))
                        (sym (assoc-sub-sub T σ₁* σ₂*)) (Eliftₛ (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂)) l T₁ x
        aux l T here = {!   !} -- subst-elim
        aux l T (there x) = {!   !} -- needs Eassoc-sub-ren and Eassoc-ren-sub

Eassoc-sub↑-sub↑ {Δ₃ = Δ₃} {σ₁* = σ₁*} {σ₂* = σ₂*} {Γ₃ = Γ₃} {T = T} {T′ = T′} e σ₁ σ₂ = 
  let ≡* = Eassoc-sub-sub e (Eliftₛ σ₁* σ₁) (Eliftₛ σ₂* σ₂) in
  begin 
    subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) (subst (Expr Δ₃ _) (assoc-sub-sub T σ₁* σ₂*) 
          (Esub σ₂* (Eliftₛ σ₂* σ₂) (Esub σ₁* (Eliftₛ σ₁* σ₁) e)))
  ≡⟨ cong (subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*)) ≡* ⟩
    subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) 
      (Esub (σ₁* ∘ₛₛ σ₂*) (Eliftₛ σ₁* σ₁ >>S Eliftₛ σ₂* σ₂) e)
  ≡⟨ cong (λ σ → subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) (Esub (σ₁* ∘ₛₛ σ₂*) σ e)) (Esub↑-dist-∘ₛₛ T′ σ₁ σ₂) ⟩
    subst (λ T′ → Expr Δ₃ (T′ ◁ Γ₃) _) (assoc-sub-sub T′ σ₁* σ₂*) 
      (Esub (σ₁* ∘ₛₛ σ₂*)
        (subst ((λ T → ESub _ _ (T ◁ Γ₃))) (sym (assoc-sub-sub T′ σ₁* σ₂*)) (Eliftₛ (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂))) 
      e)
  ≡⟨ {!   !} ⟩ -- subst elim
    Esub (σ₁* ∘ₛₛ σ₂*) (Eliftₛ (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂)) e
  ∎ 

Eassoc-sub-sub (# n) σ₁ σ₂ = refl
Eassoc-sub-sub (` x) σ₁ σ₂ = refl
Eassoc-sub-sub (ƛ e) σ₁ σ₂ = {!  !} -- use Eassoc-sub↑-sub↑
Eassoc-sub-sub {σ₁* = σ₁*} {σ₂* = σ₂*} (_·_ {T = T}{T′ = T′} e₁ e₂) σ₁ σ₂ =
  begin
    subst (Expr _ _) (assoc-sub-sub T′ σ₁* σ₂*)
      (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₁) · Esub σ₂* σ₂ (Esub σ₁* σ₁ e₂))
  ≡⟨ subst-split (Expr _ _) _·_ (assoc-sub-sub (T ⇒ T′) σ₁* σ₂*) (assoc-sub-sub T σ₁* σ₂*) (assoc-sub-sub T′ σ₁* σ₂*) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₁)) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₂)) ⟩
      (subst (Expr _ _) (assoc-sub-sub (T ⇒ T′) σ₁* σ₂*) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₁)) ·
       subst (Expr _ _) (assoc-sub-sub T σ₁* σ₂*) (Esub σ₂* σ₂ (Esub σ₁* σ₁ e₂)))
  ≡⟨ cong₂ _·_ (Eassoc-sub-sub e₁ σ₁ σ₂) (Eassoc-sub-sub e₂ σ₁ σ₂) ⟩
    (Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂) e₁ ·
       Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>S σ₂) e₂)
  ∎
Eassoc-sub-sub (Λ l ⇒ e) σ₁ σ₂ = {!  !} -- needs Eassoc-sub↑-sub↑-l
Eassoc-sub-sub (e ∙ T′) σ₁ σ₂ = {!!}


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


sub0-e′-wk-e≡e : ∀ {Δ}{Γ}{l′}{T′ : Type Δ l′}{l}{T : Type Δ l} → (e′ : Expr Δ Γ (Tsub Tidₛ T′)) (e : Expr Δ Γ T) → 
  Esub Tidₛ (sub0 e′) (Ewk e) ≡ subst (Expr Δ Γ) (sym (TidₛT≡T T)) e
sub0-e′-wk-e≡e e′ (# n) = refl
sub0-e′-wk-e≡e e′ (` x) = {! !}
sub0-e′-wk-e≡e e′ (ƛ e) = {!!}
sub0-e′-wk-e≡e e′ (e · e₁) = {!!}
sub0-e′-wk-e≡e e′ (Λ l ⇒ e) = {!!}
sub0-e′-wk-e≡e e′ (e ∙ T′) = {!!}


Eext-Elift[]~ : Eext-Elift[]~-type
Eext-Elift[]~ {.l₁} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ (.T) here =
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
    sub₁′ (sub₃ (Esub _ (sub0 (sub₂ e′)) ((Eliftₛ σ* σ) l₁ _ here)))
      ≡⟨ refl ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ _ here)
      ≡⟨ sym (dist-subst' {F = (λ a → ESub a (T ◁ Γ₁) Γ₂)} {G = Expr Δ₂ Γ₂}
                          (λ τ* → Tsub τ* T)
                          (λ f → f l₁ _ here)
                          (TSub-id-right σ*)
                          (cong (λ σ*₁ → Tsub σ*₁ T) (TSub-id-right σ*))
                          (Eliftₛ σ* σ >>S sub0 (subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) e′)))
       ⟩
    sub₁ (Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ _ here 
  ∎
Eext-Elift[]~ {l} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ T₁ (there x) =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*)) in
  let sub₁″ = subst (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁)) (TSub-id-right σ*) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T₁ σ* Tidₛ) in
  sym $ begin
    sub₁ (Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ _ (there x)
      ≡⟨ dist-subst' {F = (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂)} {G = (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁))} id (λ τ → τ l₁ _ (there x)) (TSub-id-right σ*) (TSub-id-right σ*) (Eliftₛ σ* σ >>S sub0 (sub₂ e′)) ⟩
    sub₁″ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨ sym (subst-cong (Expr Δ₂ Γ₂) (λ τ* → Tsub τ* T₁) (TSub-id-right σ*) ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ _ (there x))) ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨ refl ⟩
    sub₁′ ((Eliftₛ σ* σ >>S sub0 e′) l₁ _ (there x))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub _ (sub0 e′) (Eliftₛ σ* σ l₁ _ (there x))))
      ≡⟨ cong sub₁′ (cong sub₃ (sub0-e′-wk-e≡e {l′ = l} e′ (σ l₁ _ x))) ⟩
    sub₁′ (sub₃ ((subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T _)) (σ l₁ _ x))))
      ≡⟨ elim-subst₃ (Expr Δ₂ Γ₂)
           (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*))
           (assoc-sub-sub T₁ σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T₁))) (σ l₁ _ x)
       ⟩
    σ l₁ _ x
  ∎


-- semantic renamings on expressio
ERen* : {ρ* : TRen Δ₁ Δ₂} (TRen* : TRen* ρ* η₁ η₂) → (ρ : ERen ρ* Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → Setω
ERen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ*} Tren* ρ γ₁ γ₂ = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ _ _ x)

Ewk∈ERen* : ∀ {T : Type Δ l} (γ : Env Δ Γ η) (⟦e⟧ : ⟦ T ⟧ η) →  
  ERen* (Tren*-id η) (Ewkᵣ {T = T} Tidᵣ Eidᵣ) γ (extend γ ⟦e⟧) 
Ewk∈ERen* {η = η} {T = T} γ* ⟦e⟧ x = {!   !}

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
  let eq'' = sym (Tren*-preserves-semantics {ρ* = ρ*} {η₂ = η₂} Tren* T) in
  let eq₁ = cong (λ T₁ → inn T₁ (l₁ ◁* Γ₂)) (sym (↑ρ-TwkT≡Twk-ρT T ρ*)) in
  let eq₂ = (cong (λ T → ⟦ T ⟧ (⟦α⟧ ∷ η₂)) (sym (↑ρ-TwkT≡Twk-ρT T ρ*))) in
  let eq′ = trans (sym eq'') (trans eq' eq) in
  begin 
    extend-tskip γ₂ _ (Tren (Tliftᵣ ρ* l₁) (Twk T)) (subst id eq₁ (tskip (ρ x)))
  ≡⟨ {!   !} ⟩ -- dist subst
    subst id eq₂ (extend-tskip {⟦α⟧ = ⟦α⟧} γ₂ _ (Twk (Tren ρ* T)) (tskip (ρ x)))
  ≡⟨⟩ 
    subst id eq₂ (subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T))) (γ₂ l (Tren ρ* T) (ρ x)))
  ≡⟨ {!   !} ⟩ -- subst elim
    subst id eq′ (γ₂ l (Tren ρ* T) (ρ x))
  ≡⟨ cong (subst id eq′) eq* ⟩
    subst id eq′ (subst id eq'' (γ₁ l T x))
  ≡⟨ subst-shuffle′′′′ (γ₁ l T x) eq′ eq'' eq eq' ⟩
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
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = sym (Tren*-preserves-semantics Tren* T) in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren ρ e₁ ⟧ η₂ γ₂ (E⟦ Eren ρ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ η₁ γ₁)) (subst id eq₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ η₁ γ₁) eq₁ eq eq₂ (E⟦ e₂ ⟧ η₁ γ₁) ⟩
    subst id eq₂ (E⟦ e₁ ⟧ η₁ γ₁ (E⟦ e₂ ⟧ η₁ γ₁))
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
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tren ρ* T′) (Tren (Tliftᵣ ρ* l) T)) in
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
  ≡⟨ subst-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)  
  ∎

-- semantic substituions on expressions


subst-to-env : {σ* : TSub Δ₁ Δ₂} → ESub σ* Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ* η₂)
subst-to-env {η₂ = η₂} {σ* = σ*} σ γ₂ _ T x = subst id (subst-preserves σ* T) (E⟦ σ _ _ x ⟧ η₂ γ₂)

subst-to-env-dist-extend : {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦e⟧ : ⟦ Tsub σ* T ⟧ η₂)
  → subst-to-env (Eliftₛ {T = T} σ* σ) (extend {Γ = Γ₂} γ₂ ⟦e⟧) ≡ω extend (subst-to-env σ γ₂) (subst id (subst-preserves {η₂ = η₂} σ* T) ⟦e⟧)
subst-to-env-dist-extend {η₂ = η₂} {σ* = σ*} γ₂ σ ⟦e⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  here → refl
  (there {T′ = T′} x) →  cong (subst id (subst-preserves {η₂ = η₂} σ* T)) {!  sym (Eren*-preserves-semantics {T = Tsub σ* T} {γ₂ = γ₂} (Tren*-id η₂) (Ewk∈ERen* {T = Tsub σ* T′} γ₂ ⟦e⟧) (σ l T x))  !}

Esubst-preserves : ∀ {T : Type Δ₁ l} {η₂ : Env* Δ₂} {γ₂ : Env Δ₂ Γ₂ η₂} {σ* : TSub Δ₁ Δ₂} 
  → (σ : ESub σ* Γ₁ Γ₂) (e : Expr Δ₁ Γ₁ T)
  → E⟦ Esub σ* σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ* T)) (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))
Esubst-preserves σ (# n) = refl
Esubst-preserves {l = l} {T = T } {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (` x) =  
  sym (elim-subst id (sym (subst-preserves σ* T)) (subst-preserves σ* T) (E⟦ σ l _ x ⟧ η₂ γ₂))
Esubst-preserves {T = T ⇒ T′} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (ƛ e) = fun-ext λ ⟦e⟧ → 
  let eq* = Esubst-preserves {η₂ = η₂} {γ₂ = extend γ₂ ⟦e⟧} (Eliftₛ σ* σ) e in 
  let eq = sym (subst-preserves {η₂ = η₂} σ* (T ⇒ T′)) in 
  let eq₁ = subst-preserves {η₂ = η₂} σ* T in
  let eq₂ = (sym (subst-preserves {η₂ = η₂} σ* T′)) in
  begin 
    E⟦ Esub σ* (Eliftₛ σ* σ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env (Eliftₛ σ* σ) (extend γ₂ ⟦e⟧)))
  ≡⟨ congωl (λ γ → subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) γ)) (subst-to-env-dist-extend γ₂ σ ⟦e⟧) ⟩
    subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) (subst id eq₁ ⟦e⟧)))
  ≡⟨ dist-subst (λ ⟦e⟧ → E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) ⟦e⟧)) eq₁ eq eq₂ ⟦e⟧ ⟩
    subst id eq (λ ⟦e⟧ → E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) ⟦e⟧)) ⟦e⟧
  ∎ 
Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_·_ {T = T} {T′ = T′} e₁ e₂) = 
  let eq₁* = Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} σ e₁ in
  let eq₂* = Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} σ e₂ in 
  let eq = sym (subst-preserves {η₂ = η₂} σ* (T ⇒ T′)) in 
  let eq₁ = sym (subst-preserves {η₂ = η₂} σ* T′) in
  let eq₂ = sym (subst-preserves {η₂ = η₂} σ* T) in
  begin 
    E⟦ Esub σ* σ e₁ ⟧ η₂ γ₂ (E⟦ Esub σ* σ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))) 
    (subst id eq₂ (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)) eq₂ eq eq₁ (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)) ⟩
    subst id eq₁ (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂) (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)))
  ∎ 
Esubst-preserves {T = T′} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Esubst-preserves {η₂ = ⟦α⟧ ∷ η₂} {γ₂ = extend-tskip γ₂} (Eliftₛ-l σ* σ) e in 
  let eq₁ = (λ { ⟦α⟧ → trans (subst-preserves (Tliftₛ σ* l) T) (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ* ⟦α⟧ η₂)) }) in
  let eq = sym (dep-ext eq₁) in
  let eq′ = sym (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ* l) T) in
  let eq′′ = sym (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tdropₛ (Tliftₛ σ* l)) T′) in
  begin 
    E⟦ Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Tdropₛ (Tliftₛ σ* l)) (⟦α⟧ ∷ η₂)) (subst-to-env (Eliftₛ-l σ* σ) (extend-tskip γ₂)))
  ≡⟨ {!   !} ⟩
    subst id (sym (eq₁ ⟦α⟧)) (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂)))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) ⟦α⟧
  ∎ 
Esubst-preserves {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_∙_ {l} {T = T} e T′) = 
  let η₁ = (subst-to-env* σ* η₂) in
  let γ₁ = (subst-to-env σ γ₂) in
  let eq* = Esubst-preserves {γ₂ = γ₂} σ e in 
  let eq*' = subst-preserves {η₂ = η₂} σ* T′ in 
  let eq = (sym (σT[T′]≡σ↑T[σT'] σ* T T′)) in 
  let eq' = (sym (subst-preserves {η₂ = η₂} σ* (T [ T′ ]T))) in  
  let eq'''' = λ α → trans (subst-preserves {η₂ = α ∷ η₂} (Tliftₛ σ* l) T) (congωl (λ η → ⟦ T ⟧ (α ∷ η)) (subst-to-env*-wk σ* α η₂)) in
  let eq''''′ = λ α → trans (congωl (λ η → ⟦ T ⟧ (α ∷ η)) (symω (subst-to-env*-wk σ* α η₂))) (sym (subst-preserves (Tliftₛ σ* l) T)) in
  let eq'' = (sym (dep-ext eq'''')) in
  let eq''' = sym (subst-preserves {η₂ = ⟦ Tsub σ* T′ ⟧ η₂ ∷ η₂} (Tliftₛ σ* l) T) in
  let eq''''' = trans (congωl (λ η → ⟦ T ⟧ (⟦ Tsub σ* T′ ⟧ η₂ ∷ η)) (symω (subst-to-env*-wk σ* (⟦ Tsub σ* T′ ⟧ η₂) η₂))) eq''' in
  let eq₁ = (cong (λ T → ⟦ T ⟧ η₂) eq) in
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tsub σ* T′) (Tsub (Tliftₛ σ* l) T)) in
  let eq₃ = (sym (Tsingle-subst-preserves η₁ T′ T)) in 
  let eq₄ = cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym eq*') in
  let eq₅ = (cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym (subst-preserves {η₂ = η₂} σ* T′))) in
  begin 
    E⟦ subst (Expr Δ₂ Γ₂) eq (Esub σ* σ e ∙ Tsub σ* T′) ⟧ η₂ γ₂
  ≡⟨ {!    !} ⟩
    subst id eq₁ (subst id eq₂ ((subst id eq'' (E⟦ e ⟧ η₁ γ₁)) (⟦ Tsub σ* T′ ⟧ η₂)))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂ x)) 
     (sym (dist-subst′′ (⟦ Tsub σ* T′ ⟧ η₂) (E⟦ e ⟧ η₁ γ₁) eq'' eq''''′)) ⟩ 
    subst id eq₁ (subst id eq₂  (subst id eq''''' ((E⟦ e ⟧ η₁ γ₁) (⟦ Tsub σ* T′ ⟧ η₂))))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂  (subst id eq''''' x))) 
     (dist-subst′′′ (⟦ Tsub σ* T′ ⟧ η₂) (⟦ T′ ⟧ η₁) (E⟦ e ⟧ η₁ γ₁) (subst-preserves σ* T′) eq₅) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''''' (subst id eq₄ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))))
  ≡⟨ subst-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)
  ∎ 
      