module Fundamental4 where

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
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; subst; subst₂; resp₂; cong-app; icong;
        subst-subst; subst-∘; subst-application; subst-application′; subst-sym-subst; subst-subst-sym; -- Properties
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import BigStep
open import LogicalPrelim
open import Logical2
open import LRVren2
open import LRVsub2
open import HeterogeneousEqualityLemmas hiding (module R)

----------------------------------------------------------------------
--! Fundamental

Tsub-act-Text :
  ∀ (ρ : RelEnv Δ)
  → (T′ : Type Δ l)
  → let ρ* = subst←RE ρ in
    (l₂ : Level)
  → (x : l₂ ∈ (l ∷ Δ))
  → REext ρ (Tsub ρ* T′ ,
            subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                  (sym (subst-preserves ρ* T′))
                  (𝓥⟦ T′ ⟧ ρ)) l₂ x
  ≡ Tsub-act (Textₛ Tidₛ T′) ρ l₂ x
Tsub-act-Text ρ T′ l₂ here = refl
Tsub-act-Text ρ T′ l₂ (there x) =
  let ρ* = subst←RE ρ in
  begin
    REext ρ
      (Tsub (subst←RE ρ) T′ ,
       subst (λ ⟦T⟧ → Value (Tsub (subst←RE ρ) T′) → ⟦T⟧ → Set _)
       (sym (subst-preserves (subst←RE ρ) T′))
       (𝓥⟦ T′ ⟧ ρ))
      l₂ (there x)
  ≡⟨ refl ⟩
    ρ l₂ x
  ≡⟨ refl ⟩
    proj₁ (ρ l₂ x) , proj₂ (ρ l₂ x)
  ≡⟨ cong (proj₁ (ρ l₂ x) ,_)
    (fun-ext₂ (λ z z₁ →
      cong (proj₂ (ρ l₂ x) z)
        (sym (subst-subst-sym {P = id} (subst-var-preserves x ρ* []))))) ⟩
    proj₁ (ρ l₂ x) ,
      (λ z z₁ →
         proj₂ (ρ l₂ x) z
         (subst id (subst-var-preserves x ρ* [])
          (subst id (sym (subst-var-preserves x ρ* [])) z₁)))
  ≡⟨ cong (proj₁ (ρ l₂ x) ,_)
    (fun-ext (λ v →
      app-subst (λ z →
            proj₂ (ρ l₂ x) v (subst id (subst-var-preserves x ρ* []) z))
            (subst-var-preserves x ρ* []))) ⟩
    proj₁ (ρ l₂ x) ,
      (λ v →
         subst (λ Z → Z → Set l₂) (subst-var-preserves x ρ* [])
         (λ z →
            proj₂ (ρ l₂ x) v (subst id (subst-var-preserves x ρ* []) z)))
  ≡⟨ sym (cong (proj₁(ρ l₂ x) ,_)
         (eta-subst (λ v z → proj₂ (ρ _ x) v (subst id (subst-var-preserves x ρ* []) z))
                    (subst-var-preserves x ρ* []) )) ⟩
    proj₁(ρ l₂ x) ,
    subst (λ ⟦x⟧ → (Value (ρ* l₂ x) → ⟦x⟧ → Set _))
          (subst-var-preserves x ρ* [])
          (λ v z → proj₂ (ρ _ x) v (subst id (subst-var-preserves x ρ* []) z))
  ≡⟨ cong (π₁ ρ l₂ x ,_)
    (cong₂ (subst (λ ⟦x⟧ → Value (ρ* l₂ x) → ⟦x⟧ → Set _))
      (sym (sym-sym (subst-var-preserves x ρ* [])) ) refl) ⟩
    ρ* l₂ x ,
    subst (λ ⟦x⟧ → (Value (Tsub ρ* (` x)) → ⟦x⟧ → Set _))
          (sym (subst-preserves ρ* (` x)))
          (𝓥⟦ (` x) ⟧ ρ)
  ≡⟨ refl ⟩
    Tsub-act (Textₛ Tidₛ T′) ρ l₂ (there x)
  ∎

-- next one will become obsolete
Elift-[]≡Cextt : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (l′ l : Level) (T : Type (l ∷ Δ) l′) (e : Expr (l ∷ Δ) (l ◁* Γ) T) (T′ : Type [] l) (R : REL T′)
  → let σ = subst←RE ρ in
    let lhs = (Esub (Tliftₛ σ l) (Eliftₛ-l σ (ES←SC χ)) e [ T′ ]ET) in
    let rhs = Csub (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′)) e in
    subst (Expr [] ∅) (lemma1 ρ T T′ R) lhs ≡ rhs
Elift-[]≡Cextt Γ ρ χ l′ l T e T′ R =
  let τ* = subst←RE ρ in
  let σ = ES←SC χ in
  begin
    subst CExpr (lemma1 ρ T T′ R)
      (Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e [ T′ ]ET)  -- : Expr [] ∅ (Tsub (Tliftₛ τ* l) T [ T′ ]T)
  ≡⟨ cong (subst CExpr (lemma1 ρ T T′ R))
          ( Elift-l-[]≡Eext _ _ T′ T τ* σ e) ⟩
    subst CExpr (lemma1 ρ T T′ R)
      (subst CExpr (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T))
       (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e))
  ≡⟨  subst-subst {P = CExpr} (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T)) {(lemma1 ρ T T′ R)} {(Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e)}  ⟩
    subst CExpr
      (trans (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T)) (lemma1 ρ T T′ R))
      (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e)
  ≡⟨ subst-irrelevant {F = CExpr}
                        (trans (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T)) (lemma1 ρ T T′ R))
                        (cong (λ τ* → Tsub τ* T) (sym (subst←RE-ext-ext ρ T′ R)))
                        (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e) ⟩
    subst CExpr (cong (λ τ* → Tsub τ* T) (sym (subst←RE-ext-ext ρ T′ R)))
      (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e)   -- : Expr [] ∅ (Tsub (Textₛ τ* T′) T)
  ≡⟨ cong (λ σ → subst CExpr
      (cong (λ τ* → Tsub τ* T) (sym (subst←RE-ext-ext ρ T′ R)))
      (Esub (Textₛ (subst←RE ρ) T′) σ e))
      (sym (Cextt-Eextₛ-l {T′ = T′} χ)) ⟩
    subst CExpr (cong (λ τ* → Tsub τ* T) (sym (subst←RE-ext-ext ρ T′ R)))
    (Esub (Textₛ (subst←RE ρ) T′) (ES←SC (Cextt χ T′)) e)
  ≡⟨ refl ⟩
    subst CExpr (cong (λ τ* → Tsub τ* T) (sym (subst←RE-ext-ext ρ T′ R))) (Csub (Cextt χ T′) e)
  ≡˘⟨ dist-subst' {F = (λ τ* → CSub τ* (l ◁* Γ))} {G = CExpr} (λ τ* → Tsub τ* T) (λ χ → Csub χ e) (sym (subst←RE-ext-ext ρ T′ R)) (cong (λ τ* → Tsub τ* T) (sym (subst←RE-ext-ext ρ T′ R))) (Cextt χ T′) ⟩
    Csub
      (subst (λ τ* → CSub τ* (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R))
       (Cextt χ T′))
      e
  ∎

-- χ-val-extend :  ∀ (Γ : TEnv Δ)
--   → (ρ : RelEnv Δ)
--   → let σ* = subst←RE ρ in (χ : CSub σ* Γ)
--   → (w       : Value (Tsub (subst←RE ρ) T₁))
--   → (w ⇓ w)
--   → (∀ {l′} (T′ : Type Δ l′) (x : inn T′ Γ) → χ _ _ x ⇓ χ _ _ x)
--   → ∀ {l′} (T′ : Type Δ l′) (x : inn T′ (T₁ ◁ Γ)) →
--       Cextend χ w l′ T′ x ⇓ Cextend χ w l′ T′ x
-- χ-val-extend Γ ρ χ w w⇓w χ-val T′ here = {!!} -- need w⇓w
-- χ-val-extend Γ ρ χ w w⇓w χ-val T′ (there x₁) = χ-val T′ x₁

-- fundamental theorem

--! FundamentalType
fundamental : ∀ (Γ : TEnv Δ)
  → ∀ {l} (T : Type Δ l)
  → (e : Expr Δ Γ T)
  → (ρ : RelEnv Δ)
  → let σ* = subst←RE ρ in (χ : CSub σ* Γ)
  → let η = subst-to-env* σ* [] in (γ : Env Δ Γ η)
  → 𝓖⟦ Γ ⟧ ρ χ γ
  → 𝓔⟦ T ⟧ ρ (Csub χ e) (E⟦ e ⟧ η γ)

fundamental Γ .`ℕ (# n) ρ χ γ 𝓖⟦Γ⟧ =
  (# n , V-♯) , ⇓-n , (n , (refl , refl))

fundamental Γ .`ℕ (`suc e) ρ χ γ 𝓖⟦Γ⟧
  with fundamental Γ `ℕ e ρ χ γ 𝓖⟦Γ⟧
... | v@(# n , V-♯) , e⇓v , . n , refl , lrv =
  ((# (ℕ.suc n)) , V-♯) , ⇓-s e⇓v , ℕ.suc n  , refl , cong ℕ.suc lrv

fundamental Γ T (` x) ρ χ γ 𝓖⟦Γ⟧ =
  let w = χ _ _ x in
  let 𝓥⟦w⟧ = 𝓖-lookup Γ ρ χ γ T 𝓖⟦Γ⟧ x in
  w , Value-⇓ w , 𝓥⟦w⟧

fundamental Γ (T₁ ⇒ T₂) (ƛ e) ρ χ γ lrg =
  (Csub χ (ƛ e), V-ƛ) ,
  ⇓-ƛ ,
  Esub _ (Eliftₛ _ (ES←SC χ)) e ,
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
... | v₁@(_ , V-ƛ) , e₁⇓v₁ , e₁′ , refl , lrv₁ | v₂ , e₂⇓v₂ , lrv₂
  with lrv₁ v₂ (E⟦ e₂ ⟧ (subst-to-env* (subst←RE ρ) []) γ) lrv₂
... | v₃ , e₃[]⇓v₃ , lrv₃
  = v₃ ,
    ⇓-· e₁⇓v₁ e₂⇓v₂ e₃[]⇓v₃ ,
    lrv₃

fundamental Γ (`∀α .l , T) (Λ l ⇒ e) ρ χ γ lrg =
  (Csub χ (Λ l ⇒ e), V-Λ) ,
  ⇓-Λ ,
  Esub (Tliftₛ (subst←RE ρ) l) (Eliftₛ-l (subst←RE ρ) (ES←SC χ)) e ,
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
... | v@ (_ , V-Λ) , e⇓v , e′ , refl , lrv
  with lrv (Tsub (subst←RE ρ) T′) 
           (subst (λ ⟦T⟧ → Value (Tsub (subst←RE ρ) T′) → ⟦T⟧ → Set l) 
                  (sym (subst-preserves (subst←RE ρ) T′))
                  (𝓥⟦ T′ ⟧ ρ)) 
... | v₂ , vT′⇓v₂ , lrv₂  = 
  let ρ* = subst←RE ρ in
  let σ = ES←SC χ in
  let η = subst-to-env* ρ* [] in
  let eq₁ = sym (swap-Tsub-[] (subst←RE ρ) T T′)  in
  let e•T⇓v = ⇓-∙ e⇓v vT′⇓v₂ in
  subst Value eq₁ v₂ ,
  subst id (begin 
      Esub ρ* σ e ∙ Tsub ρ* T′ ⇓ v₂
    ≡⟨ subst-elim′′′′ (Expr [] ∅) Value _⇓_ (Esub ρ* σ e ∙ Tsub ρ* T′) v₂ eq₁ ⟩
      subst (Expr [] ∅) eq₁ (Esub ρ* σ e ∙ Tsub ρ* T′) ⇓ subst Value eq₁ v₂ 
    ∎) e•T⇓v ,
    let
      eq-sub =
        (begin
          𝓥⟦ T ⟧
            (REext ρ
             (Tsub ρ* T′ ,
              subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                (sym (subst-preserves ρ* T′))
                (𝓥⟦ T′ ⟧ ρ)))
            (subst Value
             (trans
               (trans
                (assoc-sub-sub T (Tliftₛ ρ* l)
                 (Textₛ Tidₛ (Tsub ρ* T′)))
                (trans
                 (cong (λ σ₁ → Tsub σ₁ T)
                  (sym (fun-ext₂ (sublemma-ext ρ*))))
                 refl))
               (trans
                (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂ (subst←RE-ext ρ (Tsub ρ* T′)
                       (subst
                        (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                        (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))))))
                refl))
             v₂)
            (E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ []))
        ≡⟨ cong₂
             (λ E₁ E₂ →
                𝓥⟦ T ⟧
                (REext ρ
                 (Tsub ρ* T′ ,
                  subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                  (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ)))
                (subst Value
                 (trans
                  (trans (assoc-sub-sub T (Tliftₛ ρ* l) (Textₛ Tidₛ (Tsub ρ* T′)))
                   E₁)
                  E₂)
                 v₂)
                (E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ [])))
             (trans-idʳ (cong (λ σ₁ → Tsub σ₁ T) (sym (fun-ext₂ (sublemma-ext ρ*)))))
             (trans-idʳ (cong (λ G → Tsub G T)
       (sym
        (fun-ext₂
         (subst←RE-ext ρ (Tsub ρ* T′)
          (subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
           (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))))))) ⟩
          𝓥⟦ T ⟧
            (REext ρ
             (Tsub ρ* T′ ,
              subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                (sym (subst-preserves ρ* T′))
                (𝓥⟦ T′ ⟧ ρ)))
            (subst Value
             (trans
               (trans
                (assoc-sub-sub T (Tliftₛ ρ* l)
                 (Textₛ Tidₛ (Tsub ρ* T′)))
                (cong (λ σ₁ → Tsub σ₁ T)
                  (sym (fun-ext₂ (sublemma-ext ρ*)))))
               (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂ (subst←RE-ext ρ (Tsub ρ* T′)
                       (subst
                        (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                        (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ)))))))
             v₂)
            (E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ []))
        ≡⟨ dcongωlll 𝓥⟦ T ⟧
           (relenv-ext (λ l₂ x →
             begin
               REext ρ
                 (Tsub ρ* T′ ,
                  subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                  (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                 l₂ x
             ≡⟨ Tsub-act-Text ρ T′ l₂ x ⟩
               Tsub-act (Textₛ Tidₛ T′) ρ l₂ x
             ∎))
    --------------------------------------------------
           (begin
             subst Value
               (trans
                (trans (assoc-sub-sub T (Tliftₛ ρ* l) (Textₛ Tidₛ (Tsub ρ* T′)))
                 (cong (λ σ₁ → Tsub σ₁ T) (sym (fun-ext₂ (sublemma-ext ρ*)))))
                (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂
                   (subst←RE-ext ρ (Tsub ρ* T′)
                    (subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                     (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ)))))))
               v₂
           ≡⟨ subst*-irrelevant (⟨ Value , (trans
                (trans (assoc-sub-sub T (Tliftₛ ρ* l) (Textₛ Tidₛ (Tsub ρ* T′)))
                 (cong (λ σ₁ → Tsub σ₁ T) (sym (fun-ext₂ (sublemma-ext ρ*)))))
                (cong (λ G → Tsub G T)
                 (sym
                  (fun-ext₂
                   (subst←RE-ext ρ (Tsub ρ* T′)
                    (subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                     (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))))))) ⟩∷ [])
                               (⟨ Value , (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) ⟩∷
                                ⟨ Value , (congωl (λ z → Tsub (subst←RE z) T)
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))) ⟩∷ []) v₂ ⟩
             subst Value
               (congωl (λ z → Tsub (subst←RE z) T)
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x)))))
               (subst Value (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) v₂)
           ≡⟨ sym (substω-congω Value (λ z → (Tsub (subst←RE z) T))
                                 (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
                    (subst Value (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) v₂)) ⟩
             substω (λ z → Value (Tsub (subst←RE z) T))
               (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
               (subst Value (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) v₂)
           ∎)
    --------------------------------------------------
           (begin
             E⟦ e ⟧ η γ (⟦ Tsub ρ* T′ ⟧ [])
           ≡⟨ sym (dcong (E⟦ e ⟧ η γ) (sym (subst-preserves ρ* T′))) ⟩
             subst (λ z → ⟦ T ⟧ (z ∷ η)) (sym (subst-preserves ρ* T′))
               (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
           ≡⟨ subst-∘ {P = id}{f = (λ z → ⟦ T ⟧ (z ∷ η))} (sym (subst-preserves ρ* T′)) ⟩
             subst id (cong (λ z → ⟦ T ⟧ (z ∷ η)) (sym (subst-preserves ρ* T′)))
               (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
           ≡⟨ subst-irrelevant {F = id}
                                 (cong (λ z → ⟦ T ⟧ (z ∷ η)) (sym (subst-preserves ρ* T′)))
                                 (congωl ⟦ T ⟧ (conglω (_∷ η) (sym (subst-preserves ρ* T′))))
                                 (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)) ⟩
             subst id (congωl ⟦ T ⟧ (conglω (_∷ η) (sym (subst-preserves ρ* T′)))) (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
           ≡⟨ subst*-irrelevant (⟨ id , (congωl ⟦ T ⟧ (conglω (_∷ η) (sym (subst-preserves ρ* T′)))) ⟩∷ [])
                                 (⟨ id , (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′))) ⟩∷
                                  ⟨ id , (congωl (λ z → ⟦ T ⟧ (subst-to-env* (subst←RE z) []))
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))) ⟩∷ [])
                    (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))  ⟩
             subst id
               (congωl (λ z → ⟦ T ⟧ (subst-to-env* (subst←RE z) []))
                (symω
                 (relenv-ext
                  (λ l₂ x →
                     step-≡
                     (REext ρ
                      (Tsub ρ* T′ ,
                       subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                       (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                      l₂ x)
                     (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x)))))
               (subst id
                (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
           ≡⟨ sym (substω-congω id (λ z → ⟦ T ⟧ (subst-to-env* (subst←RE z) []))
                                 (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
                    (subst id
                (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))) ⟩
             substω (λ z → ⟦ T ⟧ (subst-to-env* (subst←RE z) []))
               (symω
                (relenv-ext
                 (λ l₂ x →
                    step-≡
                    (REext ρ
                     (Tsub ρ* T′ ,
                      subst (λ ⟦T⟧ → Value (Tsub ρ* T′) → ⟦T⟧ → Set l)
                      (sym (subst-preserves ρ* T′)) (𝓥⟦ T′ ⟧ ρ))
                     l₂ x)
                    (Tsub-act (Textₛ Tidₛ T′) ρ l₂ x ∎) (Tsub-act-Text ρ T′ l₂ x))))
               (subst id
                (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
           ∎)
    --------------------------------------------------
        ⟩
          𝓥⟦ T ⟧ (Tsub-act (Textₛ Tidₛ T′) ρ)
            (subst Value (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) v₂)
            (subst id
             (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
             (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ≡⟨ LRVsub T ρ
                  (Textₛ Tidₛ T′)
                  (subst Value (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) v₂)
                  (subst id (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
                            (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ⟩
          𝓥⟦ Tsub (Textₛ Tidₛ T′) T ⟧ ρ
            (subst Value (sym (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*))
             (subst Value (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) v₂))
            (subst id
             (sym
              (step-≡ (⟦ Tsub (Textₛ Tidₛ T′) T ⟧ η)
               (trans (congωl ⟦ T ⟧ (subst-to-env*-comp (Textₛ Tidₛ T′) ρ* [])) refl)
               (subst-preserves (Textₛ Tidₛ T′) T)))
             (subst id
              (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′)))
              (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))))
        ≡⟨ cong₂ (𝓥⟦ Tsub (Textₛ Tidₛ T′) T ⟧ ρ)
          (subst*-irrelevant (⟨ Value , (trans eq₁ (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) ⟩∷
                              ⟨ Value , (sym (assoc-sub-sub T (Textₛ Tidₛ T′) ρ*)) ⟩∷
                              [])
                             (⟨ Value , eq₁ ⟩∷
                             []) v₂)
          (subst*-irrelevant (⟨ id , (cong (λ α → ⟦ T ⟧ (α ∷ η)) (sym (subst-preserves ρ* T′))) ⟩∷
                              ⟨ id , (sym
       (step-≡ (⟦ Tsub (Textₛ Tidₛ T′) T ⟧ η)
        (trans
         (congωl ⟦ T ⟧
          (conglωω _∷_ (sym (subst-preserves ρ* T′))
           (subst-to-env*-comp (Tdropₛ (Textₛ Tidₛ T′)) ρ* [])))
         refl)
        (subst-preserves (Textₛ Tidₛ T′) T))) ⟩∷ [])
                             (⟨ id , (sym
       (trans (subst-preserves (Textₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η)))) ⟩∷ [])
                             (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ⟩
          𝓥⟦ Tsub (Textₛ Tidₛ T′) T ⟧ ρ
            (subst Value eq₁ v₂)
            (subst id
             (sym
              (trans (subst-preserves (Textₛ Tidₛ T′) T)
               (congωl
                (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H))
                (subst-to-env*-id η))))
             (E⟦ e ⟧ η γ (⟦ T′ ⟧ η)))
        ∎)
    in
    subst id eq-sub lrv₂

--------------------------------------------------------------------------------

Tliftₛ-empty : ∀ {l₀} l x → Tliftₛ (λ _ ()) l₀ l x ≡ Tidₛ{Δ = l₀ ∷ []} l x
Tliftₛ-empty l here = refl

Tsub-closed : {T : Type [] l} → T ≡ Tsub (λ l ()) T
Tsub-closed {T = T₁ ⇒ T₂} = cong₂ _⇒_ Tsub-closed  Tsub-closed
Tsub-closed {T = `∀α l₀ , T} = cong (`∀α l₀ ,_)
                                    (sym (trans (cong (λ τ → Tsub τ T) (fun-ext₂ (λ l x → Tliftₛ-empty l x)))
                                                (TidₛT≡T T)))
Tsub-closed {T = `ℕ} = refl

Tsub-[]-is-Tid : ∀ (σ* : TSub [] Δ) → (λ l ()) ≡ σ*
Tsub-[]-is-Tid σ* = fun-ext λ l → fun-ext λ ()

Csub-[]-is-Eid : ∀ (χ : CSub {[]} (λ l ()) ∅) → ES←SC χ ≅ Eidₛ {Γ = ∅}
Csub-[]-is-Eid χ = fun-ext-h-ESub (Tsub-[]-is-Tid Tidₛ) refl λ l T ()

Csub-closed' : {T : Type [] l} (χ : CSub {[]} (λ l ()) ∅) → (e : CExpr T) →
  Csub χ e ≅ e
Csub-closed' {T = T} χ e =
  R.begin
    Csub χ e
  R.≅⟨ refl ⟩
    Esub (λ l ()) (ES←SC χ) e
  R.≅⟨ H.cong₂ {B = λ ■ → ESub ■ ∅ ∅} (λ ■₁ ■₂ → Esub ■₁ ■₂ e)
               (H.≡-to-≅ (Tsub-[]-is-Tid Tidₛ)) (Csub-[]-is-Eid χ) ⟩
    Esub Tidₛ Eidₛ e
  R.≅⟨ H.≡-to-≅ (Eidₛe≡e e) ⟩
    subst (Expr [] ∅) (sym (TidₛT≡T T)) e
  R.≅⟨ H.≡-subst-removable _ _ _ ⟩
    e
  R.∎

Csub-closed : {T : Type [] l} (χ : CSub {[]} (λ l ()) ∅) → (e : CExpr T) →
  Csub χ e ≡ subst CExpr Tsub-closed e
Csub-closed χ e = 
  H.≅-to-≡ (
    R.begin
      Csub χ e
    R.≅⟨ Csub-closed' χ e ⟩
      e
    R.≅⟨ H.sym (H.≡-subst-removable _ _ _) ⟩
      subst CExpr Tsub-closed e
    R.∎
  )

--! AdequacyType
adequacy : (e : CExpr `ℕ) → (n : ℕ)
  → E⟦ e ⟧ [] (λ l T → λ()) ≡ n
  → e ⇓ (# n , V-♯)

--! AdequacyBody
adequacy e n ⟦e⟧≡n
  with fundamental ∅ `ℕ e (λ l ()) (λ l T ()) (λ l T ()) tt
... | ((# .(E⟦ e ⟧ [] (λ l T ()))) , V-♯) , e⇓v , .(E⟦ e ⟧ [] (λ l T ())) , refl , refl =
  subst₂ _⇓_ (Csub-closed (λ l T ()) e) (cong (λ n → (# n) , V-♯) ⟦e⟧≡n) e⇓v

