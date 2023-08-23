{-# OPTIONS --allow-unsolved-metas #-}
module Fundamental where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _$-; λ-)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; -- Properties
        module ≡-Reasoning)
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
  χ _ x ,
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
    let lrg′ = subst₃ (LRG Γ)
                      refl -- (symω (REdrop-REext≡id ρ T′ R))
                      (sym (Cdropt-Cextt≡id Γ ρ χ l T′ R))
                      (symω (Gdropt-ext≡id ρ γ T′ R)) lrg in
    let (v , e⇓v , lrv-t)
                      = fundamental (l ◁* Γ)
                                    (REext ρ (T′ , R))
                                    (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))
                                    (extend-tskip γ)
                                    T
                                    e
                                    lrg′ in
    let v′ = subst Value (sym (lemma1 ρ T T′ R)) v in
    let e⇓v′ = subst₂ _⇓_ (sym {!Elift-[]≡Cextt Γ ρ χ _ l T e T′ R!}) {!!} e⇓v in
       v′ ,
       {!!} ,
       {!!}
    -- lemma1 ρ T T′ R : (Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T) ≡ Tsub (subst←RE (REext ρ (T′ , R))) T
fundamental Γ ρ χ γ .(T [ T′ ]T) (_∙_ {l = l}{T = T} e T′) lrg
  with fundamental Γ ρ χ γ (`∀α l , T) e lrg
... | (Λ .l ⇒ e′ , v-Λ) , e⇓v , lrv
  with lrv (Tsub (subst←RE ρ) T′) 
    (subst (λ ⟦T⟧ → Σ (Expr [] ∅ (Tsub (λ l₂ x → proj₁ (ρ l₂ x)) T′)) Val → ⟦T⟧ → Set l) (sym (subst-preserves (subst←RE ρ) T′)) ((LRV T′) ρ)) 
-- last:
--LRV (Tsub (Textₛ Tidₛ T′) T) 
--    ρ
--    (subst (λ T₁ → Σ (Expr [] ∅ T₁) Val) eq₁ v₂)
--    (subst id eq₃ (E⟦ e ⟧ (subst-to-env* σ* []) γ  (⟦ T′ ⟧ (subst-to-env* σ* []))))
----------->
--LRV T
--    (REext ρ (Tsub σ* T′ , subst (λ ⟦T⟧ →  Σ (Expr [] ∅ (Tsub σ* T′)) Val → ⟦T⟧ → Set l) (sym (subst-preserves σ* (LRV T′ ρ)))))
--    (subst (λ T₁ → Σ (Expr [] ∅ T₁) Val) eq₂? v₂)
--    (E⟦ e ⟧ (subst-to-env* σ* []) γ (⟦ Tsub σ* T′ ⟧ []))

... | v₂ , vT′⇓v₂ , lrv₂ =
  let eq₁ = sym (σT[T′]≡σ↑T[σT'] (λ l₂ x → proj₁ (ρ l₂ x)) T T′) in
  subst ((λ T → Σ (Expr [] ∅ T) Val)) eq₁ v₂ , 
  subst id (begin 
    _⇓_ (Esub (Textₛ Tidₛ (Tsub (subst←RE ρ) T′)) (Eextₛ-l Tidₛ Eidₛ) e′) v₂
    ≡⟨⟩
      _⇓_ (e′ [ (Tsub (subst←RE ρ) T′) ]ET) v₂
    ≡⟨ {!   !} ⟩ 
      _⇓_ (subst (Expr [] ∅) eq₁ (Esub (subst←RE ρ) (λ l₂ x → proj₁ (χ l₂ x)) e ∙ Tsub (subst←RE ρ) T′)) 
          (subst (λ T₁ → Σ (Expr [] ∅ T₁) Val) eq₁ v₂)
    ∎) vT′⇓v₂ , 
  {!lrv₂!}

