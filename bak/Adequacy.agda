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

open import Expressions
open import Types
open import Ext
open import SmallStep
open import SetOmega
open import ExprSubstitution

module Adequacy where

dist-subst'' :
  ∀ {ℓ₁ ℓ₂}
    {A A' : Set ℓ₁} {B B' : Set ℓ₂}
  → (f : A → B)
  → (A≡A' : A ≡ A')
  → (A→B≡A'→B' : (A → B) ≡ (A' → B'))
  → (B≡B' : B ≡ B')
  → (x : A) 
  → subst id A→B≡A'→B' f (subst id A≡A' x) ≡ subst id B≡B' (f x)
dist-subst'' _ refl refl refl _ = refl

Env-drop-level : ∀{⟦α⟧ : Set l} → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η) → Env Δ Γ η
Env-drop-level {η = η} {⟦α⟧ = ⟦α⟧} γ _ T x = 
  subst Function.id (Tren*-preserves-semantics (wkᵣ∈Ren* η ⟦α⟧) T) (γ _ _ (tskip x))

Env-drop : Env Δ (T ◁ Γ) η → Env Δ Γ η
Env-drop {η = η} γ _ _ x = γ _ _ (there x)

wkᵣ∈Ren*′ : ∀ (η₂ : Env* Δ₂) (⟦α⟧ : Set l) (σ : TSub Δ₁ Δ₂) → 
  TRen* (Twkᵣ Tidᵣ) (subst-to-env* σ η₂) (⟦α⟧ ∷ subst-to-env* (Twkₛ σ) (⟦α⟧ ∷ η₂))
wkᵣ∈Ren*′ {Δ₁ = Δ₁} η₂ ⟦α⟧ σ x = substω (λ η → apply-env η (Tidᵣ _ x) ≡ apply-env (subst-to-env* σ η₂) x) 
  {! subst-to-env*-wk ? ? ?  !} (wkᵣ∈Ren* (subst-to-env* σ η₂) ⟦α⟧ x)

Sub-to-env : ∀ {σ′ : TSub Δ₁ Δ₂} → Sub σ′ Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ′ η₂)
Sub-to-env {η₂ = η₂} {σ′ = .Tidₛ} sub-id γ _ T x = 
  substω (λ η → ⟦ T ⟧ η) (symω (subst-to-env*-id η₂)) (γ _ _ x)
Sub-to-env {Δ₁ = l ∷ Δ₁} {η₂ = _∷_ {Δ = Δ} ⟦α⟧ η₂} {σ′ = .(Tliftₛ σ′ l)} (sub-lift-l {σ = σ′} σ) γ _ .(Twk T) (tskip {T = T} x) = 
  subst id 
    (sym (Tren*-preserves-semantics (wkᵣ∈Ren*′ η₂ ⟦α⟧ σ′) T)) 
    ((Sub-to-env σ (Env-drop-level γ)) _ _ x)
Sub-to-env {η₂ = η₂} {.(Textₛ _ _)} (sub-ext {T = T′} σ) γ _ .(Twk T) (tskip {T = T} x) = 
  subst id (sym (Tren*-preserves-semantics (wkᵣ∈Ren* (subst-to-env* _ η₂) (⟦ T′ ⟧ η₂)) T)) ((Sub-to-env σ γ) _ _ x)
Sub-to-env {σ′ = σ′} (sub-lift-T  σ) γ _ T here = subst id (subst-preserves σ′ T) (γ _ _ here)
Sub-to-env {σ′ = σ′} (sub-lift-T σ) γ _ _ (there x) = (Sub-to-env σ (Env-drop γ)) _ _ x

ETRen* : {ρ′ : TRen Δ₁ Δ₂} (ρ : OPE ρ′ Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → (Tren* : TRen* ρ′ η₁ η₂)  → Setω
ETRen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ′ = ρ′} ρ γ₁ γ₂ Tren* = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ l (Tren ρ′ T) (ETren-x ρ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ l T x)

ETren*-lift-T : {ρ′ : TRen Δ₁ Δ₂} {γ₁ : Env Δ₁ Γ₁ η₁} → {γ₂ : Env Δ₂ Γ₂ η₂} {Tren* : TRen* ρ′ η₁ η₂} → {T : Type Δ₁ l} 
  (⟦e⟧ : ⟦ Tren ρ′ T ⟧ η₂) → (ρ : OPE ρ′ Γ₁ Γ₂) → ETRen* ρ γ₁ γ₂ Tren* → 
  ETRen* (ope-lift-T {T = T} ρ) (extend γ₁ (subst id (Tren*-preserves-semantics Tren* T) ⟦e⟧)) (extend γ₂ ⟦e⟧) Tren*
ETren*-lift-T ⟦e⟧ ρ ETren* here = {!   !}
ETren*-lift-T ⟦e⟧ ρ ETren* (there x) = {!   !} 

ETren*-preserves-semantics : ∀ {T : Type Δ₁ l} {ρ′ : TRen Δ₁ Δ₂} {ρ : OPE ρ′ Γ₁ Γ₂}
  {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} →
  (Tren* : TRen* ρ′ η₁ η₂) →
  (ETren* : ETRen* {ρ′ = ρ′} ρ γ₁ γ₂ Tren*) → (e : Expr Δ₁ Γ₁ T) → 
  E⟦ ETren ρ e ⟧ η₂ γ₂ ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (E⟦ e ⟧ η₁ γ₁)
ETren*-preserves-semantics Tren* ETren* (# n) = refl
ETren*-preserves-semantics Tren* ETren* (` x) = ETren* x
ETren*-preserves-semantics {ρ = ρ} Tren* ETren* (ƛ e) = fun-ext λ ⟦e⟧ → 
  {! ETren*-preserves-semantics {ρ = ope-lift-T ρ} Tren* (ETren*-lift-T ⟦e⟧ ρ ?) e !}
ETren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* ETren* (_·_ {T = T} {T′ = T′} e₁ e₂) 
  with ETren*-preserves-semantics {T = T ⇒ T′} {ρ = ρ} {γ₂ = γ₂} Tren* ETren* e₁ 
  |    ETren*-preserves-semantics {T = T} {ρ = ρ} {γ₂ = γ₂} Tren* ETren* e₂ 
... | eq₁* | eq₂* = 
  let eq = sym (Tren*-preserves-semantics Tren* T′) in
  let eq₁ = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T) in
  let sub = subst id eq in 
  let sub₁ = subst id eq₁ in
  let sub₂ = subst id eq₂ in
  begin 
    E⟦ ETren ρ e₁ ⟧ η₂ γ₂ (E⟦ ETren ρ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
   (sub₁ (E⟦ e₁ ⟧ η₁ γ₁)) (sub₂ (E⟦ e₂ ⟧ η₁ γ₁))
  ≡⟨ dist-subst'' (E⟦ e₁ ⟧ η₁ γ₁) eq₂ eq₁ eq (E⟦ e₂ ⟧ η₁ γ₁) ⟩
    sub (E⟦ e₁ ⟧ η₁ γ₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ∎
ETren*-preserves-semantics Tren* ETren* (Λ l ⇒ e) = {!   !}
ETren*-preserves-semantics Tren* ETren* (e ∙ T′) = {!   !}

ETsubst-preserves : ∀ {T : Type Δ₁ l} {σ′ : TSub Δ₁ Δ₂} 
  (η₂ : Env* Δ₂) (γ₂ : Env Δ₂ Γ₂ η₂) → (σ : Sub σ′ Γ₁ Γ₂) → (e : Expr Δ₁ Γ₁ T) → 
  E⟦ ETsub σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ′ T)) (E⟦ e ⟧ (subst-to-env* σ′ η₂) (Sub-to-env σ γ₂))
ETsubst-preserves η₂ γ₂ σ (# n) = refl
ETsubst-preserves η₂ γ₂ σ (` x) = {!   !}
ETsubst-preserves η₂ γ₂ σ (ƛ e) = {!   !}
ETsubst-preserves η₂ γ₂ σ (e₁ · e₂) 
  with ETsubst-preserves η₂ γ₂ σ e₁ 
  |    ETsubst-preserves η₂ γ₂ σ e₂
... | a | b = {!   !}
ETsubst-preserves η₂ γ₂ σ (Λ l ⇒ e) = {!   !}
ETsubst-preserves η₂ γ₂ σ (e ∙ T′) = {!   !}

ERen* : (ρ : ERen Γ₁ Γ₂) → (γ₁ : Env Δ Γ₁ η) → (γ₂ : Env Δ Γ₂ η) → Setω
ERen* {Δ = Δ} {Γ₁ = Γ₁} ρ γ₁ γ₂ = ∀ {l} {T : Type Δ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ x) ≡ γ₁ _ _ x

Ewkᵣ∈ERen* : {T : Type Δ l} (⟦e⟧ : ⟦ T ⟧ η) → ERen* (Ewkᵣ {T = T} Eidᵣ) γ (extend γ ⟦e⟧)
Ewkᵣ∈ERen* ⟦e⟧ x = refl

Eren*-id : (γ : Env Δ Γ η) → ERen* Eidᵣ γ γ
Eren*-id γ x = refl

Eren*-lift : ∀ {ρ : ERen Γ₁ Γ₂} {T : Type Δ l} (⟦e⟧ : ⟦ T ⟧ η) → 
  ERen* ρ γ₁ γ₂ → ERen* (Eliftᵣ {T = T} ρ) (extend γ₁ ⟦e⟧) (extend γ₂ ⟦e⟧)
Eren*-lift ⟦e⟧ Eren* here = refl
Eren*-lift ⟦e⟧ Eren* (there x) = Eren* x

Eren*-lift-l : ∀ {ρ : ERen Γ₁ Γ₂} {γ₁ : Env Δ Γ₁ η} {γ₂ : Env Δ Γ₂ η} {l : Level} (⟦α⟧ : Set l) → 
  ERen* ρ γ₁ γ₂ → ERen* (Eliftᵣ-l {l = l} ρ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₁) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₂)
Eren*-lift-l {η = η} ⟦α⟧ Eren* (tskip {T = T} x) 
  rewrite Tren*-preserves-semantics {ρ = Twkᵣ Tidᵣ} {η} {⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T = Eren* x

Eren*-preserves-semantics : {ρ : ERen Γ₁ Γ₂} {γ₁ : Env Δ Γ₁ η} {γ₂ : Env Δ Γ₂ η} →
  (Eren* : ERen* ρ γ₁ γ₂) → (e : Expr Δ Γ₁ T) → E⟦ Eren ρ e ⟧ η γ₂ ≡ E⟦ e ⟧ η γ₁
Eren*-preserves-semantics Eren* (# n) = refl
Eren*-preserves-semantics Eren* (` x) = Eren* x
Eren*-preserves-semantics Eren* (ƛ e) = fun-ext λ ⟦e⟧ → 
  Eren*-preserves-semantics (Eren*-lift ⟦e⟧ Eren*) e
Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Eren* (e₁ · e₂) 
  rewrite Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Eren* e₁ |
          Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Eren* e₂   
          = refl
Eren*-preserves-semantics Eren* (Λ l ⇒ e) = fun-ext λ ⟦α⟧ → 
  Eren*-preserves-semantics (Eren*-lift-l ⟦α⟧ Eren*) e
Eren*-preserves-semantics {η = η} Eren* (_∙_ {T = T} e T′) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (Eren*-preserves-semantics Eren* e) (⟦ T′ ⟧ η)

subst-to-env : ESub Γ₁ Γ₂ → Env Δ Γ₂ η → Env Δ Γ₁ η
subst-to-env {η = η} σ γ₂ _ _ x = E⟦ σ x ⟧ η γ₂

ste-dist-ext : ∀ (σ : ESub Γ₁ Γ₂) (T : Type Δ l) (⟦e⟧ : ⟦ T ⟧ η) (γ : Env Δ Γ₂ η) → 
  subst-to-env (Eliftₛ {T = T} σ) (extend {T = T} γ ⟦e⟧) ≡ω extend {T = T} (subst-to-env σ γ) ⟦e⟧
ste-dist-ext σ T ⟦e⟧ γ = fun-ext-lvl λ _ → fun-ext₂ λ where 
  _ here → refl
  _ (there x) → Eren*-preserves-semantics {ρ = Ewkᵣ Eidᵣ} (Ewkᵣ∈ERen* {γ = γ} {T = T} ⟦e⟧) (σ x)

ste-dist-ext-tskip : ∀ (σ : ESub Γ₁ Γ₂) (l : Level) (⟦α⟧ : Set l) (γ : Env Δ Γ₂ η) → 
  subst-to-env (Eliftₛ-l {l = l} σ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ) ≡ω (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ))   
ste-dist-ext-tskip {Δ = Δ} {Γ₁ = Γ₁} {η = η} σ l ⟦α⟧ γ = fun-ext-lvl λ _ → fun-ext₂ λ { _ (tskip x) → 
  ETren*-preserves-semantics (wkᵣ∈Ren* η ⟦α⟧) {!   !} (σ x) }

Esubst-preserves : ∀ (γ : Env Δ Γ₂ η) → (σ : ESub Γ₁ Γ₂) (e : Expr Δ Γ₁ T)
  → E⟦ Esub σ e ⟧ η γ ≡ E⟦ e ⟧ η (subst-to-env σ γ)
Esubst-preserves γ σ (# n) = refl
Esubst-preserves γ σ (` x) = refl
Esubst-preserves {η = η} γ σ (ƛ_ {T = T} e) = fun-ext λ ⟦e⟧ → 
  trans (Esubst-preserves (extend γ ⟦e⟧) (Eliftₛ σ) e) 
        (congωl (E⟦ e ⟧ η) (ste-dist-ext σ T ⟦e⟧ γ))
Esubst-preserves γ σ (e₂ · e₁) rewrite Esubst-preserves γ σ e₁ | Esubst-preserves γ σ e₂ = refl
Esubst-preserves {η = η} γ σ (Λ l ⇒ e) = fun-ext λ ⟦α⟧ → 
  trans (Esubst-preserves (extend-tskip γ) (Eliftₛ-l σ) e) 
        (congωl (E⟦ e ⟧ (⟦α⟧ ∷ η)) (ste-dist-ext-tskip σ l ⟦α⟧ γ))
Esubst-preserves {η = η} γ σ (_∙_ {T = T} e T′) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (Esubst-preserves γ σ e) (⟦ T′ ⟧ η)

{-
E⟦ Esub (Eextₛ `_ e₂) e₁ ⟧ η γ ≡
      E⟦ e₁ ⟧ η (extend γ (E⟦ e₂ ⟧ η γ))
Have
E⟦ Esub (Eextₛ `_ e₂) e₁ ⟧ η γ ≡
      E⟦ e₁ ⟧ η (λ z z₁ x → E⟦ Eextₛ `_ e₂ x ⟧ η γ)
-}
Esingle-subst-preserves : ∀ (γ : Env Δ Γ η) (e₁ : Expr Δ (T′ ◁ Γ) T) (e₂ : Expr Δ Γ T′) →
  E⟦ e₁ [ e₂ ]E ⟧ η γ ≡ E⟦ e₁ ⟧ η (extend γ (E⟦ e₂ ⟧ η γ))  
Esingle-subst-preserves {η = η} γ e₁ e₂ = 
  substω (λ γ′ → E⟦ Esub (Eextₛ `_ e₂) e₁ ⟧ η γ ≡ E⟦ e₁ ⟧ η γ′) {! refl  !} 
  (Esubst-preserves γ (Eextₛ Eidₛ e₂) e₁)

adequacy : ∀ {e₁ e₂ : Expr Δ Γ T} → e₁ ↪ e₂ → E⟦ e₁ ⟧ η γ ≡ E⟦ e₂ ⟧ η γ
adequacy {γ = γ} (β-ƛ {e₂ = e₂} {e₁ = e₁} v₂) = sym (Esingle-subst-preserves γ e₁ e₂)
adequacy {η = η} (β-Λ {T = T} {T′ = T′}) = {!   !}
  -- rewrite Tsingle-subst-preserves η T T′ = ?
adequacy {η = η} {γ = γ} (ξ-·₁ {e₂ = e₂} e₁↪e) = cong-app (adequacy e₁↪e) (E⟦ e₂ ⟧ η γ)
adequacy {η = η} {γ = γ} (ξ-·₂ {e₁ = e₁} e₂↪e v₁) = cong (E⟦ e₁ ⟧ η γ) (adequacy e₂↪e)
adequacy {η = η} {γ = γ} (ξ-∙ {T′ = T′} {T = T} e₁↪e₂) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (adequacy e₁↪e₂) (⟦ T′ ⟧ η)  