{-# OPTIONS --allow-unsolved-metas #-} 
module Soundness where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_])
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst; subst-sym-subst; sym-cong;
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
module R = H.≅-Reasoning
open import HeterogeneousSetωEquality as Hω using (_≅ω_; refl)
module Rω = Hω.≅ω-Reasoning

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstFusion public
open import SmallStep
import HeterogeneousEqualityLemmas as HE

-- semantic renamings on expression
ERen* : {ρ* : TRen Δ₁ Δ₂} (TRen* : TRen* ρ* η₁ η₂) → (ρ : ERen ρ* Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → Setω
ERen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ*} Tren* ρ γ₁ γ₂ = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ _ _ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ _ _ x)

Ewk-l∈ERen* : ∀ (γ : Env Δ Γ η) (⟦α⟧ : Set l) →  
  ERen* (wkᵣ∈Ren* η ⟦α⟧) (Ewkᵣ-l l) γ (extend-tskip {⟦α⟧ = ⟦α⟧} γ)
Ewk-l∈ERen* {η = η} γ* ⟦α⟧ x = refl 

Ewk∈ERen* : ∀ {T : Type Δ l} (γ : Env Δ Γ η) (⟦e⟧ : ⟦ T ⟧ η) →  
  ERen* (Tren*-id η) (Ewkᵣ {T = T} Tidᵣ Eidᵣ) γ (extend γ ⟦e⟧) 
Ewk∈ERen* {η = η} γ* ⟦e⟧ {T = T} x = H.≅-to-≡ (R.begin 
    γ* _ (Tren Tidᵣ T) (subst (λ T → inn T _) (sym (TidᵣT≡T T)) x)
  R.≅⟨ H.cong₂ (γ* _) (H.≡-to-≅ (TidᵣT≡T T)) (H.≡-subst-removable (λ T → inn T _) (sym (TidᵣT≡T T)) _) ⟩
    (γ* _ T x)
  R.≅⟨ H.sym (H.≡-subst-removable id (sym (Tren*-preserves-semantics (Tren*-id η) T)) _) ⟩
    subst id (sym (Tren*-preserves-semantics (Tren*-id η) T)) (γ* _ T x)
  R.∎)

ERen*-lift : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦e⟧ : ⟦ Tren ρ* T ⟧ η₂) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* Tren* (Eliftᵣ {T = T} _ ρ) (extend γ₁ (subst id (Tren*-preserves-semantics Tren* T) ⟦e⟧)) (extend γ₂ ⟦e⟧)
ERen*-lift {η₁ = η₁} {η₂ = η₂} {T = T} {ρ* = ρ*} ⟦e⟧ Tren* Eren* here 
  rewrite Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T = refl
ERen*-lift {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} ⟦e⟧ Tren* Eren* {T = T} (there x) = Eren* x

ERen*-lift-l : ∀ {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦α⟧ : Set l) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* (Tren*-lift ⟦α⟧ Tren*) (Eliftᵣ-l _ ρ) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₁) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₂)
ERen*-lift-l {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {l = l₁} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦α⟧ Tren* Eren* {l} (tskip {T = T} x) =
  let eq* = Eren* x in 
  let eq = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) (Twk T)) in 
  let eq' = sym (Tren*-preserves-semantics (wkᵣ∈Ren* η₁ ⟦α⟧) T) in 
  let eq'' = sym (Tren*-preserves-semantics {ρ* = ρ*} {η₂ = η₂} Tren* T) in
  let eq₁ = cong (λ T₁ → inn T₁ (l₁ ◁* Γ₂)) (sym (swap-Tren-Twk ρ* T)) in
  let eq₂ = (cong (λ T → ⟦ T ⟧ (⟦α⟧ ∷ η₂)) (sym (swap-Tren-Twk ρ* T))) in
  let eq′ = trans (sym eq'') (trans eq' eq) in
  H.≅-to-≡(R.begin 
    extend-tskip γ₂ l (Tren (Tliftᵣ ρ* l₁) (Twk T)) (subst id eq₁ (tskip (ρ _ T x)))
  R.≅⟨ H.cong₂ (extend-tskip γ₂ l) (H.≡-to-≅ (swap-Tren-Twk ρ* T)) (H.≡-subst-removable id eq₁ _) ⟩ 
    extend-tskip γ₂ l (Twk (Tren ρ* T)) (tskip (ρ _ _ x))
  R.≅⟨ H.sym (H.≡-subst-removable id eq₂ _) ⟩ 
    subst id eq₂ (extend-tskip γ₂ _ (Twk (Tren ρ* T)) (tskip (ρ _ _ x)))
  R.≅⟨ refl ⟩ 
    subst id eq₂ (subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T))) (γ₂ l (Tren ρ* T) (ρ _ _ x)))
  R.≅⟨ H.≡-to-≅ (subst-shuffle′′′′ ((γ₂ l (Tren ρ* T) (ρ _ _ x))) eq₂ ((sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T)))) eq′ refl) ⟩ 
    subst id eq′ (γ₂ l (Tren ρ* T) (ρ _ _ x))
  R.≅⟨ H.≡-to-≅ (cong (subst id eq′) eq*) ⟩
    subst id eq′ (subst id eq'' (γ₁ l T x))
  R.≅⟨ H.≡-to-≅ (subst-shuffle′′′′ (γ₁ l T x) eq′ eq'' eq eq') ⟩
    subst id eq (subst id eq' (γ₁ l T x))
  R.∎)

Eren*-preserves-semantics : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} →
  (Tren* : TRen* ρ* η₁ η₂) →
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  (e : Expr Δ₁ Γ₁ T) → 
  E⟦ Eren ρ* ρ e ⟧ η₂ γ₂ ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (E⟦ e ⟧ η₁ γ₁)
Eren*-preserves-semantics Tren* Eren* (# n) = refl
Eren*-preserves-semantics Tren* Eren* (`suc n) = cong ℕ.suc (Eren*-preserves-semantics Tren* Eren* n)
Eren*-preserves-semantics Tren* Eren* (` x) = Eren* x
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(T ⇒ T′)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (ƛ_ {T = T} {T′} e) = fun-ext λ ⟦e⟧ →
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ ρ* ρ} {γ₂ = extend γ₂ ⟦e⟧} Tren* (ERen*-lift {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦e⟧ Tren* Eren*) e  in
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = Tren*-preserves-semantics Tren* T in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren ρ* (Eliftᵣ ρ* ρ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
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
    E⟦ Eren _ ρ e₁ ⟧ η₂ γ₂ (E⟦ Eren _ ρ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ η₁ γ₁)) (subst id eq₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ η₁ γ₁) eq₁ eq eq₂ (E⟦ e₂ ⟧ η₁ γ₁) ⟩
    subst id eq₂ (E⟦ e₁ ⟧ η₁ γ₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(`∀α l , T)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ-l _ ρ} {γ₁ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₁} {γ₂ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₂} 
            (Tren*-lift {η₁ = η₁} ⟦α⟧ Tren*) (ERen*-lift-l ⟦α⟧ Tren* Eren*) e in 
  let eq₁ = (λ { ⟦α⟧ → Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T }) in
  let eq = sym (dep-ext eq₁) in 
  let eq₂ = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T) in
  begin 
    E⟦ Eren _ (Eliftᵣ-l _ ρ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) ⟦α⟧
  ∎
Eren*-preserves-semantics {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_∙_ {l} {T = T} e T′) = 
  let eq* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e in 
  let eq*' = Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T′ in 
  let eq = (sym (swap-Tren-[] ρ* T T′)) in 
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
    E⟦ subst (Expr Δ₂ Γ₂) eq (Eren _ ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Eren ρ* ρ e ∙ Tren ρ* T′) ⟩
    subst id eq₁ (E⟦ (Eren ρ* ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂)
  ≡⟨⟩
    subst id eq₁ (subst id eq₂ (E⟦ (Eren ρ* ρ e) ⟧ η₂ γ₂ (⟦ Tren ρ* T′ ⟧ η₂)))
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

-- -- semantic substituions on expressions


subst-to-env : {σ* : TSub Δ₁ Δ₂} → ESub σ* Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ* η₂)
subst-to-env {η₂ = η₂} {σ* = σ*} σ γ₂ _ T x = subst id (subst-preserves σ* T) (E⟦ σ _ _ x ⟧ η₂ γ₂)

subst-to-env-dist-extend : {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦e⟧ : ⟦ Tsub σ* T ⟧ η₂)
  → subst-to-env (Eliftₛ {T = T} σ* σ) (extend {Γ = Γ₂} γ₂ ⟦e⟧) ≡ω extend (subst-to-env σ γ₂) (subst id (subst-preserves {η₂ = η₂} σ* T) ⟦e⟧)
subst-to-env-dist-extend {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₂ = η₂} {T = T₂} {σ* = σ*} γ₂ σ ⟦e⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  here → refl
  (there {T′ = T′} x) → cong (subst id (subst-preserves {η₂ = η₂} σ* T)) (H.≅-to-≡(R.begin 
     E⟦ Ewk (σ l T x) ⟧ η₂ (extend γ₂ ⟦e⟧)
   R.≅⟨ refl ⟩
    E⟦ subst (Expr Δ₂ (Tsub σ* T₂ ◁ Γ₂)) (TidᵣT≡T (Tsub σ* T)) (Eren _ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T x)) ⟧ η₂ (extend γ₂ ⟦e⟧)
   R.≅⟨ H.cong {y = Ewk (σ l T x)} (λ ∎ → E⟦_⟧ {T = Tsub σ* T} ∎ η₂ (extend γ₂ ⟦e⟧)) (H.≡-subst-removable (Expr Δ₂ (Tsub σ* T₂ ◁ Γ₂)) refl _) ⟩
    E⟦ Ewk {Δ = Δ₂} (σ l T x) ⟧ η₂ (extend γ₂ ⟦e⟧)
   R.≅⟨ refl ⟩
    E⟦ subst (Expr Δ₂ (Tsub σ* T₂ ◁ Γ₂)) (TidᵣT≡T (Tsub σ* T)) (Eren _ (Ewkᵣ {l = _} {T = Tsub σ* T′} Tidᵣ Eidᵣ) (σ l T x)) ⟧ η₂ (extend γ₂ ⟦e⟧)
   R.≅⟨ H.cong₂ (λ T ∎ → E⟦_⟧ {T = T} ∎ η₂ (extend γ₂ ⟦e⟧)) (H.≡-to-≅ (sym (TidᵣT≡T (Tsub σ* T)))) (H.≡-subst-removable (Expr Δ₂ (Tsub σ* T₂ ◁ Γ₂)) (TidᵣT≡T (Tsub σ* T)) _) ⟩
    E⟦ (Eren _ (Ewkᵣ {l = _} {T = Tsub σ* T′} Tidᵣ Eidᵣ) (σ l T x)) ⟧ η₂ (extend γ₂ ⟦e⟧)
   R.≅⟨ H.≡-to-≅ (Eren*-preserves-semantics (Tren*-id η₂) (Ewk∈ERen* {l = _} {T = Tsub σ* T′} γ₂ ⟦e⟧) (σ l T x)) ⟩
    subst id (sym (Tren*-preserves-semantics (Tren*-id η₂) (Tsub σ* T))) (E⟦ σ l T x ⟧ η₂ γ₂)
   R.≅⟨ H.≡-subst-removable id (sym (Tren*-preserves-semantics (Tren*-id η₂) (Tsub σ* T))) _ ⟩
    E⟦ σ l T x ⟧ η₂ γ₂
   R.∎))

subst-to-env-dist-extend-l : {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦α⟧ : Set l)
  → subst-to-env (Eliftₛ-l {l = l} σ* σ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₂) ≡ω 
    substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))
subst-to-env-dist-extend-l {Δ₁ = Δ₁} {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₂ = η₂} {Γ₁ = Γ₁} {l = l₁} {σ* = σ*} γ₂ σ ⟦α⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  (tskip {T = T₁} x) →
    (H.≅-to-≡(R.begin 
      subst-to-env (Eliftₛ-l σ* σ) (extend-tskip γ₂) l (Twk T₁) (tskip x)
    R.≅⟨ refl ⟩
      subst id (subst-preserves (Tliftₛ σ* l₁) (Tren (Twkᵣ Tidᵣ) T₁)) (E⟦ subst (Expr (_ ∷ Δ₂) (_ ◁* Γ₂)) ((sym
        (trans (fusion-Tsub-Tren T₁ (λ z x₁ → there x₁) (Tliftₛ σ* l₁))
         (trans (sym (fusion-Tren-Tsub T₁ σ* (λ z x₁ → there x₁))) refl)))) 
      (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l _) (σ l T₁ x)) ⟧  (⟦α⟧ ∷ η₂) (extend-tskip γ₂))
    R.≅⟨ H.≡-subst-removable id (subst-preserves (Tliftₛ σ* l₁) (Tren (Twkᵣ Tidᵣ) T₁)) _ ⟩
      E⟦ subst (Expr (_ ∷ Δ₂) (_ ◁* Γ₂)) (sym
        (trans (fusion-Tsub-Tren T₁ (λ z x₁ → there x₁) (Tliftₛ σ* l₁))
         (trans (sym (fusion-Tren-Tsub T₁ σ* (λ z x₁ → there x₁))) refl)))
      (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l _) (σ l T₁ x)) ⟧  (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
    R.≅⟨ H.cong₂ (λ T ∎ → E⟦_⟧ {T = T} ∎ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)) (H.≡-to-≅ ((
        (trans (fusion-Tsub-Tren T₁ (λ z x₁ → there x₁) (Tliftₛ σ* l₁))
         (trans (sym (fusion-Tren-Tsub T₁ σ* (λ z x₁ → there x₁))) refl))))) (H.≡-subst-removable ((Expr (_ ∷ Δ₂) (_ ◁* Γ₂))) ((sym
        (trans (fusion-Tsub-Tren T₁ (λ z x₁ → there x₁) (Tliftₛ σ* l₁))
         (trans (sym (fusion-Tren-Tsub T₁ σ* (λ z x₁ → there x₁))) refl)))) _) ⟩
      E⟦ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l _) (σ l T₁ x)) ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
    R.≅⟨ H.≡-to-≅ (Eren*-preserves-semantics (wkᵣ∈Ren* η₂ ⟦α⟧) (Ewk-l∈ERen* γ₂ ⟦α⟧) (σ l T₁ x)) ⟩
      subst id (sym (Tren*-preserves-semantics (wkᵣ∈Ren* η₂ ⟦α⟧) (Tsub σ* T₁))) (E⟦ σ l T₁ x ⟧ η₂ γ₂)
    R.≅⟨ H.≡-subst-removable id (sym (Tren*-preserves-semantics (wkᵣ∈Ren* η₂ ⟦α⟧) (Tsub σ* T₁))) _ ⟩ 
      E⟦ σ l T₁ x ⟧ η₂ γ₂
    R.≅⟨ H.sym (H.≡-subst-removable id ((subst-preserves σ* T₁)) _) ⟩ 
      (subst id (subst-preserves σ* T₁) (E⟦ σ l T₁ x ⟧ η₂ γ₂))
    R.≅⟨ H.sym (H.≡-subst-removable id ((sym (Tren*-preserves-semantics (λ x₁ → refl) T₁))) _) ⟩ 
      (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂)) l (Twk T₁) (tskip x)
    R.≅⟨ H.sym (Hω.cong₂-ωωl {B = λ η → Env (l₁ ∷ Δ₁) (l₁ ◁* Γ₁)
      (⟦α⟧ ∷ η)} (λ _ ■ → ■ l (Twk T₁) (tskip x)) (Hω.≡ω-to-≅ω (subst-to-env*-wk _ ⟦α⟧ η₂)) (Hω.≡ω-substωω-removable ((Env (_ ∷ Δ₁) (_ ◁* Γ₁))) ((congωω (_∷_ ⟦α⟧) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂)))) _)) ⟩
      substωω 
        (Env (_ ∷ Δ₁) (_ ◁* Γ₁)) 
        (congωω (_∷_ ⟦α⟧) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) 
        (extend-tskip (subst-to-env σ γ₂)) 
      l (Twk T₁) (tskip x)
    R.∎))

Esubst-preserves : ∀ {T : Type Δ₁ l} {η₂ : Env* Δ₂} {γ₂ : Env Δ₂ Γ₂ η₂} {σ* : TSub Δ₁ Δ₂} 
  → (σ : ESub σ* Γ₁ Γ₂) (e : Expr Δ₁ Γ₁ T)
  → E⟦ Esub σ* σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ* T)) (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))
Esubst-preserves σ (# n) = refl
Esubst-preserves σ (`suc n) = cong ℕ.suc (Esubst-preserves σ n)
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
  (H.≅-to-≡(R.begin 
    E⟦ Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  R.≅⟨ H.≡-to-≅ eq* ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) (subst-to-env (Eliftₛ-l σ* σ) (extend-tskip γ₂)))
  R.≅⟨ H.≡-to-≅ (congωl (λ γ → subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) γ)) (subst-to-env-dist-extend-l γ₂ σ ⟦α⟧)) ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) (substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))))
  R.≅⟨ H.≡-subst-removable id eq′ _ ⟩
    (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) (substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))))
  R.≅⟨ Hω.cong₂-ωωl E⟦ e ⟧ (Hω.≡ω-to-≅ω (congωω (⟦α⟧ ∷_) (subst-to-env*-wk _ ⟦α⟧ η₂))) (Hω.≡ω-substωω-removable ((Env _ _)) ((congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂)))) _) ⟩
    (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂)))
  R.≅⟨ H.sym (H.≡-subst-removable id ((sym (eq₁ ⟦α⟧))) _) ⟩
    subst id (sym (eq₁ ⟦α⟧)) (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂)))
  R.≅⟨ H.≡-to-≅ (dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧))) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) ⟦α⟧
  R.∎))
Esubst-preserves {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_∙_ {l} {T = T} e T′) = 
  let η₁ = (subst-to-env* σ* η₂) in
  let γ₁ = (subst-to-env σ γ₂) in
  let eq* = Esubst-preserves {γ₂ = γ₂} σ e in 
  let eq*' = subst-preserves {η₂ = η₂} σ* T′ in 
  let eq = (sym (swap-Tsub-[] σ* T T′)) in 
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
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Esub σ* σ e ∙ Tsub σ* T′) ⟩
    subst id eq₁ (subst id eq₂ (E⟦ Esub σ* σ e ⟧ η₂ γ₂ (⟦ Tsub σ* T′ ⟧ η₂)))
  ≡⟨ cong (λ e → subst id eq₁ (subst id eq₂ (e (⟦ Tsub σ* T′ ⟧ η₂)))) eq* ⟩
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
   
EEsingle-subst-preserves : ∀ (γ : Env Δ Γ η) (e₁ : Expr Δ (T′ ◁ Γ) T) (e₂ : Expr Δ Γ T′) →
  E⟦ e₁ [ e₂ ]E ⟧ η γ ≡ E⟦ e₁ ⟧ η (extend γ (E⟦ e₂ ⟧ η γ))  
EEsingle-subst-preserves {Δ = Δ} {Γ = Γ} {η = η} {T′ = T′} {T = T} γ e₁ e₂ = 
  (H.≅-to-≡(R.begin 
   E⟦ subst (Expr Δ Γ) (TidₛT≡T T) (Esub (λ z → `_) (Eextₛ (λ z → `_) (λ z T₁ x → subst (Expr Δ Γ) (sym (TidₛT≡T T₁)) (` x)) (subst (Expr Δ Γ) (sym (TidₛT≡T T′)) e₂)) e₁)  ⟧ η γ
  R.≅⟨ H.cong₂ (λ T ∎ → E⟦_⟧ {T = T} ∎ η γ) (H.≡-to-≅ (sym (TidₛT≡T T))) (H.≡-subst-removable (Expr Δ Γ) (TidₛT≡T T) _) ⟩
   E⟦ (Esub (λ z → `_) (Eextₛ (λ z → `_) (λ z T₁ x → subst (Expr Δ Γ) (sym (TidₛT≡T T₁)) (` x)) (subst (Expr Δ Γ) (sym (TidₛT≡T T′)) e₂)) e₁) ⟧ η γ
  R.≅⟨ H.≡-to-≅ (Esubst-preserves {η₂ = η} {γ₂ = γ} (sub0 (subst (Expr _ _) (sym (TidₛT≡T _))  e₂)) e₁) ⟩ 
   subst id (sym (subst-preserves Tidₛ T))
      (E⟦ e₁ ⟧ (subst-to-env* Tidₛ η)
       (subst-to-env (sub0 (subst (Expr Δ Γ) (sym (TidₛT≡T T′)) e₂)) γ))
  R.≅⟨ H.≡-subst-removable id (sym (subst-preserves Tidₛ T)) _ ⟩ 
    E⟦ e₁ ⟧ (subst-to-env* Tidₛ η)
       (subst-to-env (sub0 (subst (Expr Δ Γ) (sym (TidₛT≡T T′)) e₂)) γ)
  R.≅⟨ Hω.cong-ωl (E⟦ e₁ ⟧ (subst-to-env* Tidₛ η)) (Hω.≡ω-to-≅ω (lemma {e = e₂})) ⟩ 
    E⟦ e₁ ⟧ (subst-to-env* Tidₛ η) (substωω (Env _ _) (symω (subst-to-env*-id η)) (extend γ (E⟦ e₂ ⟧ η γ)))
  R.≅⟨ Hω.cong₂-ωωl E⟦ e₁ ⟧ (Hω.≡ω-to-≅ω (subst-to-env*-id {Δ = Δ} η)) (Hω.≡ω-substωω-removable (Env _ _) (symω (subst-to-env*-id η)) _) ⟩ 
    E⟦ e₁ ⟧ η (extend γ (E⟦ e₂ ⟧ η γ))
  R.∎))
  where lemma : ∀ {l} {Δ} {Γ} {η} {γ} {T : Type Δ l} {e : Expr Δ Γ T} → 
                 subst-to-env (sub0 {T₁ = T} (subst (Expr Δ Γ) (sym (TidₛT≡T T)) e)) γ ≡ω substωω (Env _ _) (symω (subst-to-env*-id η)) (extend γ (E⟦ e ⟧ η γ))
        lemma = {!   !}

ETsingle-subst-preserves : ∀ (γ : Env Δ Γ η) (e : Expr (l ∷ Δ) (l ◁* Γ) T′) (T : Type Δ l) →
  E⟦ e [ T ]ET ⟧ η γ ≡ subst id (sym (Tsingle-subst-preserves η T T′)) (E⟦ e ⟧ (⟦ T ⟧ η ∷ η) (extend-tskip γ))
ETsingle-subst-preserves {Δ = Δ} {Γ = Γ} {η = η} {T′ = T′} γ e T = (H.≅-to-≡(R.begin 
    E⟦ e [ T ]ET ⟧ η γ
  R.≅⟨ refl ⟩ 
    E⟦ Esub (Textₛ Tidₛ T) (Eextₛ-l Tidₛ Eidₛ) e ⟧ η γ
  R.≅⟨ H.≡-to-≅ (Esubst-preserves (Eextₛ-l Tidₛ Eidₛ) e) ⟩ 
    subst id (sym (subst-preserves ((Textₛ Tidₛ T)) T′)) (E⟦ e ⟧ (subst-to-env* (Textₛ Tidₛ T) η) (subst-to-env (Eextₛ-l {T = T} Tidₛ Eidₛ) γ))
  R.≅⟨ H.≡-subst-removable id ((sym (subst-preserves ((Textₛ Tidₛ T)) T′))) _ ⟩ 
    E⟦ e ⟧ (subst-to-env* (Textₛ Tidₛ T) η) (subst-to-env (Eextₛ-l {T = T} Tidₛ Eidₛ) γ)
  R.≅⟨ Hω.cong₂-ωωl E⟦ e ⟧ (Hω.≡ω-to-≅ω (congωω (⟦ T ⟧ η ∷_) (subst-to-env*-id η))) 
        (Rω.begin 
          (subst-to-env (Eextₛ-l Tidₛ Eidₛ) γ) 
        Rω.≅ω⟨ Hω.≡ω-to-≅ω lemma ⟩ (substωω (Env _ _) (congωω (⟦ T ⟧ η ∷_) (symω (subst-to-env*-id η))) (extend-tskip γ)) 
        Rω.≅ω⟨ Hω.≡ω-substωω-removable ((Env _ _)) (congωω (⟦ T ⟧ η ∷_) (symω (subst-to-env*-id η))) _ ⟩ 
          (extend-tskip γ) 
        Rω.∎) ⟩
    E⟦ e ⟧ (⟦ T ⟧ η ∷ η) (extend-tskip γ)
  R.≅⟨ H.sym (H.≡-subst-removable id (sym (Tsingle-subst-preserves η T T′)) _) ⟩
    subst id (sym (Tsingle-subst-preserves η T T′)) (E⟦ e ⟧ (⟦ T ⟧ η ∷ η) (extend-tskip γ))
  R.∎))
  where lemma : ∀ {l} {Δ} {Γ} {η} {γ} {T : Type Δ l} → 
                subst-to-env {Γ₂ = Γ} (Eextₛ-l {T = T} Tidₛ Eidₛ) γ ≡ω substωω (Env _ _) (congωω (⟦ T ⟧ η ∷_) (symω (subst-to-env*-id η))) (extend-tskip γ)
        lemma = {!   !}

soundness : ∀ {e₁ e₂ : Expr Δ Γ T} → e₁ ↪ e₂ → E⟦ e₁ ⟧ η γ ≡ E⟦ e₂ ⟧ η γ
soundness β-suc = refl
soundness (ξ-suc e₁↪e₂) = cong ℕ.suc (soundness e₁↪e₂)
soundness {γ = γ} (β-ƛ {e₂ = e₂} {e₁ = e₁} v₂) = sym (EEsingle-subst-preserves γ e₁ e₂)
soundness {γ = γ} (β-Λ {T = T} {e = e}) = sym (ETsingle-subst-preserves γ e T)
soundness {η = η} {γ = γ} (ξ-·₁ {e₂ = e₂} e₁↪e) = cong-app (soundness e₁↪e) (E⟦ e₂ ⟧ η γ)
soundness {η = η} {γ = γ} (ξ-·₂ {e₁ = e₁} e₂↪e v₁) = cong (E⟦ e₁ ⟧ η γ) (soundness e₂↪e)
soundness {η = η} {γ = γ} (ξ-∙ {T′ = T′} {T = T} e₁↪e₂) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (soundness e₁↪e₂) (⟦ T′ ⟧ η)  