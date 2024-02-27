{-# OPTIONS --allow-unsolved-metas #-}
module Fundamental where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; -- Properties
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Extensionality
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import SmallStep
open import Logical

----------------------------------------------------------------------

-- fundamental theorem

fundamental : ∀ (Γ : TEnv Δ) (ρ : RelEnv Δ)
  → (χ : CSub (subst←RE ρ) Γ)
  → let η = subst-to-env* (subst←RE ρ) [] in (γ : Env Δ Γ η)
  → ∀ {l} (T : Type Δ l) (e : Expr Δ Γ T)
  → LRG Γ ρ χ γ
  → ∃[ v ] (Csub χ e ⇓ v) ∧ LRV T ρ v (E⟦ e ⟧ η γ)
fundamental Γ ρ χ γ T (` x) lrg =
  χ _ _ x ,
  exp-v⇓v _ ,
  LRV←LRG Γ ρ χ γ T lrg x
fundamental Γ ρ χ γ `ℕ (# n) lrg =
  V-ℕ n ,
  ⇓-n ,
  refl
fundamental Γ ρ χ γ {.(l ⊔ l′)} (_⇒_ {l} {l′} T T′) (ƛ e) lrg =
  (Csub χ (ƛ e) , v-ƛ) ,
  ⇓-ƛ ,
  (λ w z lrv-w-z →
    let lrg′ = (lrv-w-z , substlω (LRG Γ ρ) (sym (Cdrop-Cextend {T = T} χ w)) (ENVdrop-extend {T = T} γ z) lrg) in
    let r = fundamental (T ◁ Γ) ρ (Cextend χ w) (extend γ z) T′ e lrg′ in
    case r of λ where
      (v , ew⇓v , lrv-v) → v ,
                           subst (_⇓ v) (Cextend-Elift{l′ = l′}{T′} χ w e) ew⇓v ,
                           lrv-v
    )
fundamental Γ ρ χ γ T (_·_ {T = T₂}{T′ = .T} e₁ e₂) lrg
  with fundamental Γ ρ χ γ (T₂ ⇒ T) e₁ lrg | fundamental Γ ρ χ γ T₂ e₂ lrg
... | (e₃ , v-ƛ) , e₁⇓v₁ , lrv₁ | v₂ , e₂⇓v₂ , lrv₂
  with lrv₁ v₂ (E⟦ e₂ ⟧ (subst-to-env* (subst←RE ρ) []) γ) lrv₂
... | v₃ , e₃[]⇓v₃ , lrv₃
  =
  v₃ ,
  (⇓-· e₁⇓v₁ e₂⇓v₂ e₃[]⇓v₃) ,
  lrv₃
fundamental Γ ρ χ γ (`∀α l , T) (Λ .l ⇒ e) lrg =
  (Csub χ (Λ l ⇒ e) , v-Λ) ,
  ⇓-Λ ,
  λ T′ R →
    let lrg′ = substωlω-l (LRG Γ)
                      refl -- (symω (REdrop-REext≡id ρ T′ R))
                      (sym (Cdropt-Cextt≡id Γ ρ χ l T′ R))
                      (symω (Gdropt-ext≡id ρ γ T′ R)) lrg in
    fundamental (l ◁* Γ)
                (REext ρ (T′ , R))
                (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))
                (extend-tskip γ)
                T
                e
                lrg′
    |> λ where
      (v , e⇓v , lrv-t) → 
        let v′ = subst Value (sym (lemma1 ρ T T′ R)) v in
        let e⇓v = subst₂ _⇓_ (sym (Elift-[]≡Cextt Γ ρ χ _ l T e T′ R)) refl e⇓v in
        let sub-lrvt = subst₂ (LRV T (REext ρ (T′ , R))) (sym (subst-subst-sym (lemma1 ρ T T′ R))) refl in
        let σ* = subst←RE ρ in
        let σ = ES←SC χ in
        let 𝕖 = Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ) (Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e) in
        let eq = lemma1 ρ T T′ R in
           v′ ,
           subst id (begin 
              subst (Expr [] ∅) eq 𝕖 ⇓ v
            ≡⟨ subst-swap′′ (Expr [] ∅) Value _⇓_ 𝕖 v (sym eq) eq ⟩
              𝕖 ⇓ subst Value (sym eq) v
            ∎) e⇓v ,
           sub-lrvt lrv-t
fundamental Γ ρ χ γ .(T [ T′ ]T) (_∙_ {l = l}{T = T} e T′) lrg
  with fundamental Γ ρ χ γ (`∀α l , T) e lrg
... | (Λ .l ⇒ e′ , v-Λ) , e⇓v , lrv
  with lrv (Tsub (subst←RE ρ) T′) 
           (subst (λ ⟦T⟧ → Value (Tsub (subst←RE ρ) T′) → ⟦T⟧ → Set l) 
                  (sym (subst-preserves (subst←RE ρ) T′))
                  ((LRV T′) ρ)) 
... | v₂ , vT′⇓v₂ , lrv₂ =
  let σ* = subst←RE ρ in
  let σ = ES←SC χ in
  let η = subst-to-env* σ* [] in
  let eq₁ = sym (σT[T′]≡σ↑T[σT'] (subst←RE ρ) T T′) in
  let eq₂ = (sym (subst-preserves σ* T′)) in
  let eq₃ = {!   !} in
  let eq₄ = {!   !} in
  let eq₅ = {!   !} in
  let e•T⇓v = ⇓-∙ e⇓v vT′⇓v₂ in
  subst Value eq₁ v₂ , 
  subst id (begin 
      Esub σ* σ e ∙ Tsub σ* T′ ⇓ v₂
    ≡⟨ subst-elim′′′′ (Expr [] ∅) Value _⇓_ (Esub σ* σ e ∙ Tsub σ* T′) v₂ eq₁ ⟩
      subst (Expr [] ∅) eq₁ (Esub σ* σ e ∙ Tsub σ* T′) ⇓ subst Value eq₁ v₂ 
    ∎) e•T⇓v ,
  subst id (begin 
      LRV T                                                                                        -- | connected 
          (REext ρ (Tsub σ* T′ , subst (λ ⟦T⟧ → Value (Tsub σ* T′) → ⟦T⟧ → Set l) eq₂ (LRV T′ ρ)))  -- | to each other
          (subst Value eq₃ v₂) -- easy
          (E⟦ e ⟧ η γ (⟦ Tsub σ* T′ ⟧ [])) -- easy
    ≡⟨ {!   !} ⟩
      LRV (T [ T′ ]T) 
          ρ 
          (subst Value eq₄ v₂) -- easy
          (subst id eq₅ (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))) -- easy
    ∎) lrv₂

-- gets better when switching to Logical1!
Csub-closed : {T : Type [] l} (χ : CSub {[]} (λ l → λ()) ∅) → (e : Expr [] ∅ T) →
  Csub χ e ≡ subst (Expr _ _) {!!} e
Csub-closed χ e = {!!}

adequacy : (e : Expr [] ∅ `ℕ) → (n : ℕ)
  → E⟦ e ⟧ [] (λ l T → λ()) ≡ n
  → e ⇓ V-ℕ n
adequacy e n ⟦e⟧≡n
  with fundamental ∅ (λ l → λ()) (λ l T → λ()) (λ l T → λ()) `ℕ e tt
... | #m , e⇓#m , lrv-ℕ-m-E⟦e⟧
  with #m in eq
... | # m , v-n
  rewrite trans lrv-ℕ-m-E⟦e⟧ ⟦e⟧≡n = subst (_⇓ V-ℕ n) (Csub-closed (λ l T → λ()) e) e⇓#m
