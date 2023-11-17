{-# OPTIONS --allow-unsolved-metas #-}
module Fundamental2 where

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

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import Logical1
open import LRVren

----------------------------------------------------------------------

𝓥⟦w⟧⇒w⇓w : ∀ {l} → (T : Type Δ l) (ρ : RelEnv Δ) (w : Value (Tsub (subst←RE ρ) T)) (z : ⟦ T ⟧ (subst-to-env* (subst←RE ρ) [])) → 𝓥⟦ T ⟧ ρ w z → w ⇓ w
𝓥⟦w⟧⇒w⇓w (` α) ρ w z (w⇓w , _) = w⇓w
𝓥⟦w⟧⇒w⇓w (T₁ ⇒ T₂) ρ .(ƛ e) z (e , refl , _) = ⇓-ƛ
𝓥⟦w⟧⇒w⇓w (`∀α l , T) ρ w z (e , refl , _) = ⇓-Λ
𝓥⟦w⟧⇒w⇓w `ℕ ρ w z (n , refl , _) = ⇓-n

-- next one will become obsolete
Elift-[]≡Cextt : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (l′ l : Level) (T : Type (l ∷ Δ) l′) (e : Expr (l ∷ Δ) (l ◁* Γ) T) (T′ : Type [] l) (R : REL T′)
  → let lhs = (Esub (Tliftₛ (subst←RE ρ) l) (Eliftₛ-l (subst←RE ρ) χ) e [ T′ ]ET) in
    let rhs = Csub (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′)) e in
    subst (Expr [] ∅) (lemma1 ρ T T′ R) lhs ≡ rhs
Elift-[]≡Cextt Γ ρ χ l′ l T e T′ R = {!!}


-- fundamental theorem

fundamental : ∀ (Γ : TEnv Δ)
  → ∀ {l} (T : Type Δ l)
  → (e : Expr Δ Γ T)
  → (ρ : RelEnv Δ)
  → let σ* = subst←RE ρ in (χ : CSub σ* Γ)
  → let η = subst-to-env* σ* [] in (γ : Env Δ Γ η)
  → 𝓖⟦ Γ ⟧ ρ χ γ
  → 𝓔⟦ T ⟧ ρ (Csub χ e) (E⟦ e ⟧ η γ)

fundamental Γ .`ℕ (# n) ρ χ γ 𝓖⟦Γ⟧ =
  # n , ⇓-n , n , (refl , refl)

fundamental Γ T (` x) ρ χ γ 𝓖⟦Γ⟧ =
  let w = χ _ _ x in
  let 𝓥⟦w⟧ = 𝓖-lookup Γ ρ χ γ T 𝓖⟦Γ⟧ x in
  w , 𝓥⟦w⟧⇒w⇓w T ρ w _ 𝓥⟦w⟧ , 𝓥⟦w⟧

fundamental Γ (T₁ ⇒ T₂) (ƛ e) ρ χ γ lrg =
  Csub χ (ƛ e) ,
  ⇓-ƛ ,
  Esub _ (Eliftₛ _ χ) e ,
  refl ,
  (λ w z lrv-w-z →
    let lrg′ = (lrv-w-z , substlω (𝓖⟦ Γ ⟧ ρ) (sym (Cdrop-Cextend {T = T₁} χ w)) (ENVdrop-extend {T = T₁} γ z) lrg) in
    let r = fundamental (T₁ ◁ Γ) T₂ e ρ (Cextend χ w) (extend γ z) lrg′ in
    case r of λ where
      (v , ew⇓v , lrv-v) → v ,
                           subst (_⇓ v) (Cextend-Elift χ w e) ew⇓v ,
                           lrv-v)

fundamental Γ T (_·_ {T = T₂} {T′ = .T} e₁ e₂) ρ χ γ lrg
  with fundamental Γ (T₂ ⇒ T) e₁ ρ χ γ lrg | fundamental Γ T₂ e₂ ρ χ γ lrg
... | v₁ , e₁⇓v₁ , e₁′ , refl , lrv₁ | v₂ , e₂⇓v₂ , lrv₂
  with lrv₁ v₂ (E⟦ e₂ ⟧ (subst-to-env* (subst←RE ρ) []) γ) lrv₂
... | v₃ , e₃[]⇓v₃ , lrv₃
  = v₃ ,
    ⇓-· e₁⇓v₁ e₂⇓v₂ e₃[]⇓v₃ ,
    lrv₃

fundamental Γ (`∀α .l , T) (Λ l ⇒ e) ρ χ γ lrg = 
  Csub χ (Λ l ⇒ e) ,
  ⇓-Λ ,
  Esub (Tliftₛ (subst←RE ρ) l) (Eliftₛ-l (subst←RE ρ) χ) e ,
  refl ,
  λ T′ R →
    let lrg′ = substωlω-l (𝓖⟦ Γ ⟧)
                      refl
                      (sym (Cdropt-Cextt≡id Γ ρ χ l T′ R))
                      (symω (Gdropt-ext≡id ρ γ T′ R)) lrg in
    fundamental (l ◁* Γ)
                T
                e
                (REext ρ (T′ , R))
                (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))
                (extend-tskip γ)
                lrg′
    |> λ where
      (v , e⇓v , lrv-t) → 
        let v′ = subst Value (sym (lemma1 ρ T T′ R)) v in
        let e⇓v = subst₂ _⇓_ (sym (Elift-[]≡Cextt Γ ρ χ _ l T e T′ R)) refl e⇓v in
        let sub-lrvt = subst₂ (𝓥⟦ T ⟧ (REext ρ (T′ , R))) (sym (subst-subst-sym (lemma1 ρ T T′ R))) refl in
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

fundamental Γ .(T [ T′ ]T) (_∙_ {l = l}{T = T} e  T′) ρ χ γ lrg
  with fundamental Γ (`∀α l , T) e ρ χ γ lrg
... | v , e⇓v , e′ , refl , lrv
  with lrv (Tsub (subst←RE ρ) T′) 
           (subst (λ ⟦T⟧ → Value (Tsub (subst←RE ρ) T′) → ⟦T⟧ → Set l) 
                  (sym (subst-preserves (subst←RE ρ) T′))
                  (𝓥⟦ T′ ⟧ ρ)) 
... | v₂ , vT′⇓v₂ , lrv₂  = 
  let σ* = subst←RE ρ in
  let σ = ES←SC χ in
  let η = subst-to-env* σ* [] in
  let eq₁ = sym (σT[T′]≡σ↑T[σT'] (subst←RE ρ) T T′) in
  let eq₂ = (sym (subst-preserves σ* T′)) in
  let e•T⇓v = ⇓-∙ e⇓v vT′⇓v₂ in
  subst Value eq₁ v₂ ,
  subst id (begin 
      Esub σ* σ e ∙ Tsub σ* T′ ⇓ v₂
    ≡⟨ subst-elim′′′′ (Expr [] ∅) Value _⇓_ (Esub σ* σ e ∙ Tsub σ* T′) v₂ eq₁ ⟩
      subst (Expr [] ∅) eq₁ (Esub σ* σ e ∙ Tsub σ* T′) ⇓ subst Value eq₁ v₂ 
    ∎) e•T⇓v ,
  {!lrv₂!}



-- -- adequacy : (e : Expr [] ∅ `ℕ) → (n : ℕ)
-- --   → E⟦ e ⟧ [] (λ l T → λ()) ≡ n
-- --   → e ⇓ V-ℕ n
-- -- adequacy e n ⟦e⟧≡n
-- --   with fundamental ∅ (λ l → λ()) (λ l T → λ()) (λ l T → λ()) `ℕ e tt
-- -- ... | #m , e⇓#m , lrv-ℕ-m-E⟦e⟧
-- --   with #m in eq
-- -- ... | # m , v-n
-- --   rewrite trans lrv-ℕ-m-E⟦e⟧ ⟦e⟧≡n = subst (_⇓ V-ℕ n) (Csub-closed (λ l T → λ()) e) e⇓#m
