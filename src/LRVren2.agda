module LRVren2 where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; _,′_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_; _∘₂_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; sym-cong; -- Properties
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
open import BigStep
open import Logical2

----------------------------------------------------------------------
--! LRVren >

--! LRVrenEqType
LRVren-eq′ :  ∀ {Δ₁}{Δ₂}{l}
  → (T : Type Δ₁ l)
  → (ρ : RelEnv Δ₂)
  → (τ* : TRen Δ₁ Δ₂)
  → (v : Value (Tsub (τ* ∘ᵣₛ subst←RE ρ) T))
  → (z : ⟦ T ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []))
  → let σ* = subst←RE ρ
  in 𝓥⟦ T ⟧ (Tren-act τ* ρ) v z ≡
    subst₂ (λ vv zz → Value vv → zz → Set l)
           (assoc-sub-ren T τ* σ*)
           (Tren*-preserves-semantics {ρ* = τ*}{subst-to-env* (subst←RE (Tren-act τ* ρ)) []}{subst-to-env* σ* []} (τ*∈Ren* τ* σ*) T)
           (𝓥⟦ Tren τ* T ⟧ ρ) v z

LRVren-eq′ `ℕ ρ τ* v z = refl

LRVren-eq′ {l = l} (` α) ρ τ* v z = 
  begin
    proj₂ (Tren-act τ* ρ l α) v
      (subst id
       (sym (subst-var-preserves α (subst←RE (Tren-act τ* ρ)) [])) z)
  ≡⟨ cong (proj₂ (ρ l (τ* l α)) v)
     (trans (subst-irrelevant (sym (subst-var-preserves α (subst←RE (Tren-act τ* ρ)) [])) _ z) (sym (subst-subst {P = id} (sym (τ*∈Ren* τ* (subst←RE ρ) α)) {y≡z = (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) }))) ⟩
    proj₂ (ρ l (τ* l α)) v
      (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) []))
       (subst id (sym (τ*∈Ren* τ* (subst←RE ρ) α)) z))
  ≡⟨ cong (λ H → H z) (app-subst (λ z₁ →
         proj₂ (ρ l (τ* l α)) v
         (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) z₁)) (τ*∈Ren* τ* (subst←RE ρ) α)) ⟩
    subst (λ Z → Z → Set l) (τ*∈Ren* τ* (subst←RE ρ) α)
      (λ z₁ →
         proj₂ (ρ l (τ* l α)) v
         (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) z₁))
      z
  ≡˘⟨ cong (λ H → H v z) (eta-subst (λ v₁ z₁ →
         proj₂ (ρ l (τ* l α)) v₁
         (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) z₁)) (τ*∈Ren* τ* (subst←RE ρ) α)) ⟩
    subst (λ zz → Value (proj₁ (ρ l (τ* l α))) → zz → Set l)
      (τ*∈Ren* τ* (subst←RE ρ) α)
      (λ v₁ z₁ →
         proj₂ (ρ l (τ* l α)) v₁
         (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) z₁))
      v z
  ≡˘⟨ cong (λ H → H v z) (subst₂→subst (λ vv zz → Value vv → zz → Set l) (τ*∈Ren* τ* (subst←RE ρ) α) (λ v₁ z₁ →
         proj₂ (ρ l (τ* l α)) v₁
         (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) z₁))) ⟩
    subst₂ (λ vv zz → Value vv → zz → Set l) refl
      (τ*∈Ren* τ* (subst←RE ρ) α)
      (λ v₁ z₁ →
         proj₂ (ρ l (τ* l α)) v₁
         (subst id (sym (subst-var-preserves (τ* l α) (subst←RE ρ) [])) z₁))
      v z
  ∎
LRVren-eq′ (T₁ ⇒ T₂) ρ τ* v z =
  begin
    𝓥⟦ T₁ ⇒ T₂ ⟧ (Tren-act τ* ρ) v z
  ≡⟨⟩
    (∃[ e ]
         (exp v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
  ≡⟨⟩
     Σ (Expr [] (Tsub (subst←RE (Tren-act τ* ρ)) T₁ ◁ ∅) (Tsub (subst←RE (Tren-act τ* ρ)) T₂))
     (λ e → (exp v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
  ≡⟨ sigma-subst (λ e → (exp v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
         (cong₂ (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) ⟩
    Σ (Expr [] (Tsub (subst←RE ρ) (Tren τ* T₁) ◁ ∅) (Tsub (subst←RE ρ) (Tren τ* T₂)))
      (λ e →
         (exp v ≡
          (ƛ
           subst id
           (sym (cong₂ (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e))
         ∧
         ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ →
             (subst id
              (sym (cong₂ (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
              e
              [ exp w ]E)
             ⇓ v₁
             ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
  ≡⟨ cong (Σ _) (fun-ext (λ e →
     cong₂ _∧_
     ------------------------------
     (begin
       (exp v ≡
     (ƛ
      subst id
      (sym (cong₂ (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
      e))
    ≡⟨ cong (exp v ≡_) (cong (λ eq → ƛ subst id eq e) (sym-cong₂ _ (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) ⟩
      exp v ≡
     (ƛ
      subst id
      (cong₂ (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂) (sym (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))) (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
      e)
    ≡˘⟨ cong (exp v ≡_) (cong ƛ_ (subst₂-∘ id (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂) (sym (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))) (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) e)) ⟩
      (exp v ≡
       (ƛ
        subst₂ (id ∘₂ (λ t₁ t₂ → Expr [] (t₁ ◁ ∅) t₂))
        (sym (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))))
        (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) e))
    ≡˘⟨ cong (exp v ≡_) (subst-split-ƛ (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)) (sym (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))) (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) e) ⟩
      (exp v ≡
       subst CExpr
       (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))
       (ƛ e))
    ≡⟨ subst-swap-eq′ {F = CExpr} (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)) (exp v) (ƛ e) ⟩
      (subst CExpr
       (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))
       (exp v)
       ≡ (ƛ e))
    ≡˘⟨ cong (_≡ ƛ e) (dist-subst' {F = Value} {G = CExpr} id exp (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) v) ⟩
      (exp
       (subst Value (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))
        v)
       ≡ (ƛ e))
    ≡⟨ cong (_≡ (ƛ e)) (cong exp (subst-∘ {P = id} {f = Value} (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) {v})) ⟩
      (exp
       (subst id
        (cong Value
         (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))))
        v)
       ≡ (ƛ e))
    ≡˘⟨  cong (_≡ (ƛ e)) (cong (λ eq → exp (subst id eq v)) (sym-cong {f = Value} (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) ⟩
      (exp
       (subst id
        (sym (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) v)
       ≡ (ƛ e))
    ∎)
     ------------------------------
     (begin
       ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
        (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
       𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp w ]E)
          ⇓ v₁
          ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁)))
    ≡⟨ pi-subst
         (λ w →
            (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
            𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
            ∃-syntax
            (λ v₁ →
               (subst id
                (sym
                 (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                  (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                  (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                e
                [ exp w ]E)
               ⇓ v₁
               ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁)))
         (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) ⟩
      (((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
       (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
       𝓥⟦ T₁ ⟧ (Tren-act τ* ρ)
       (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w) z₁ →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
    ≡⟨ dep-ext (λ w →
      begin 
        ((z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
               𝓥⟦ T₁ ⟧ (Tren-act τ* ρ)
       (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w) z₁ →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁)))
      ≡⟨ pi-subst
           (λ z₁ →
              𝓥⟦ T₁ ⟧ (Tren-act τ* ρ)
              (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w) z₁ →
              ∃-syntax
              (λ v₁ →
                 (subst id
                  (sym
                   (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                    (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                    (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                  e
                  [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
                  ]E)
                 ⇓ v₁
                 ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁)))
           (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁) ⟩
        (((z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
           𝓥⟦ T₁ ⟧ (Tren-act τ* ρ)
           (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁) →
           ∃-syntax
           (λ v₁ →
              (subst id
               (sym
                (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                 (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                 (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
               e
               [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
               ]E)
              ⇓ v₁
              ∧
              𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
              (z
               (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                z₁)))))
      ≡⟨ dep-ext (λ z₁ → 
        begin (𝓥⟦ T₁ ⟧ (Tren-act τ* ρ)
       (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
        z₁) →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁))))
      ≡⟨ cong (λ A → A → ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁)))) (LRVren-eq′ T₁ ρ τ* (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w) (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁) z₁))
        ⟩
           ((subst₂ (λ vv zz → Value vv → zz → Set _)
           (assoc-sub-ren T₁ τ* (subst←RE ρ))
           (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
           (𝓥⟦ Tren τ* T₁ ⟧ ρ)
           (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁) →
           ∃-syntax
           (λ v₁ →
              (subst id
               (sym
                (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                 (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                 (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
               e
               [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
               ]E)
              ⇓ v₁
              ∧
              𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
              (z
               (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                z₁)))))
      ≡⟨ cong (λ H → H 
       (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
        z₁) →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁)))) (subst₂-∘₁ (λ vv zz → vv → zz → Set _) Value (assoc-sub-ren T₁ τ* (subst←RE ρ)) (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁) (𝓥⟦ Tren τ* T₁ ⟧ ρ) ) ⟩
        (subst₂ (λ vv zz → vv → zz → Set _)
           (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ)))
           (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
           (𝓥⟦ Tren τ* T₁ ⟧ ρ)
           (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁) →
           ∃-syntax
           (λ v₁ →
              (subst id
               (sym
                (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                 (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                 (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
               e
               [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
               ]E)
              ⇓ v₁
              ∧
              𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
              (z
               (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                z₁))))
      ≡⟨ cong (λ H → H 
       (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
        z₁) →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁)))) (eta-subst₂ (𝓥⟦ Tren τ* T₁ ⟧ ρ) (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁) ) ⟩
        ((𝓥⟦ Tren τ* T₁ ⟧ ρ
       (subst id (sym (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))))
        (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w))
       (subst id
        (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁))
        (subst id
         (Tren*-preserves-semantics (λ v₁ → τ*∈Ren* τ* (subst←RE ρ) v₁) T₁)
         z₁)) →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁)))))
      ≡⟨ cong (λ A → A → ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁))))
            (begin
              𝓥⟦ Tren τ* T₁ ⟧ ρ
                  (subst id (sym (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))))
                   (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w))
                  (subst id
                   (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁))
                   (subst id
                    (Tren*-preserves-semantics (λ v₁ → τ*∈Ren* τ* (subst←RE ρ) v₁) T₁)
                    z₁))
            ≡⟨ cong (λ H → 𝓥⟦ Tren τ* T₁ ⟧ ρ H
      (subst id
       (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁))
       (subst id
        (Tren*-preserves-semantics (λ v₁ → τ*∈Ren* τ* (subst←RE ρ) v₁) T₁)
        z₁))) (subst-sym-subst {P = id} (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) {p = w}) ⟩
              𝓥⟦ Tren τ* T₁ ⟧ ρ w
                  (subst id
                   (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁))
                   (subst id
                    (Tren*-preserves-semantics (λ v₁ → τ*∈Ren* τ* (subst←RE ρ) v₁) T₁)
                    z₁))
            ≡⟨ cong (𝓥⟦ Tren τ* T₁ ⟧ ρ w) (subst-sym-subst {P = id} (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁) {p = z₁} ) ⟩
              𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁
            ∎)
         ⟩
        (𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
       ∃-syntax
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁))))
      ≡⟨ cong (λ A → 𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ → A)
        ----------------------------------------
        (begin
        Σ (Value (Tsub (τ* ∘ᵣₛ subst←RE ρ) T₂))
       (λ v₁ →
          (subst id
           (sym
            (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
             (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
             (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
           e
           [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
           ]E)
          ⇓ v₁
          ∧
          𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
          (z
           (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
            z₁)))
          ≡⟨ sigma-subst
               (λ v₁ →
                  (subst id
                   (sym
                    (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                     (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                     (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                   e
                   [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
                   ]E)
                  ⇓ v₁
                  ∧
                  𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁
                  (z
                   (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                    z₁)))
               (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) ⟩
          Σ (Value (Tsub (subst←RE ρ) (Tren τ* T₂)))
      (λ a′ →
         (subst id
          (sym
           (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
            (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
            (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
          e
          [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
          ]E)
         ⇓
         subst id
         (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) a′
         ∧
         𝓥⟦ T₂ ⟧ (Tren-act τ* ρ)
         (subst id
          (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) a′)
         (z
          (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
           z₁)))
         ≡⟨ cong (Σ _) (fun-ext (λ v₁ →
         ------------------------------
         cong₂ _∧_
           (begin
             (subst id
             (sym
              (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
               (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
               (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
             e
             [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
             ]E)
            ⇓
            subst id
            (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁
           ≡⟨ cong (λ H → (subst id
             (sym
              (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
               (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
               (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
             e
             [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
             ]E)
            ⇓
            subst id H v₁) (sym-cong {f = Value} (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))
            ⟩
             (subst id
       (sym
        (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
         (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
         (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
       e
       [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       ]E)
      ⇓
      subst id
      (cong Value (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁
           ≡⟨ cong (λ H → (subst id
       (sym
        (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
         (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
         (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
       e
       [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       ]E)
      ⇓ H) (sym (subst-∘ {P = id}{f = Value} (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) {p = v₁})) ⟩
             (subst id
       (sym
        (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
         (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
         (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
       e
       [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       ]E)
      ⇓
      subst Value (sym (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) v₁
           ≡⟨ sym (subst-split-eq-⇓ (subst id
       (sym
        (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
         (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
         (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
       e
       [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
       ]E) v₁ (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))
            ⟩
             subst CExpr (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
                (subst id
                 (sym
                  (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                   (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                   (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                 e
                 [ exp (subst id (cong Value (assoc-sub-ren T₁ τ* (subst←RE ρ))) w)
                 ]E)
                ⇓ v₁
           ≡˘⟨ cong (λ H → subst CExpr (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
      (subst id
       (sym
        (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
         (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
         (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
       e [ exp H ]E)
      ⇓ v₁) (subst-∘ {P = id}{f = Value} (assoc-sub-ren T₁ τ* (subst←RE ρ)) {p = w}) ⟩
             subst CExpr (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
                (subst id
                 (sym
                  (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                   (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                   (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                 e
                 [ exp (subst Value (assoc-sub-ren T₁ τ* (subst←RE ρ)) w)
                 ]E)
                ⇓ v₁
           ≡⟨ cong (λ H → subst CExpr (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
                (subst id
                 (sym
                  (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                   (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                   (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                 e [ H ]E)
                ⇓ v₁) ( dist-subst' {F = Value} {G = CExpr} id exp (assoc-sub-ren T₁ τ* (subst←RE ρ)) (assoc-sub-ren T₁ τ* (subst←RE ρ)) w ) ⟩
             subst CExpr (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
                 (subst id
                  (sym
                   (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                    (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                    (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                  e
                  [ subst CExpr (assoc-sub-ren T₁ τ* (subst←RE ρ)) (exp w) ]E)
                 ⇓ v₁ 
           ≡⟨ cong (_⇓ v₁) (subst-split-[]E′ (subst id
                  (sym
                   (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                    (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                    (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                  e) (exp w) (assoc-sub-ren T₁ τ* (subst←RE ρ)) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))) ) ⟩
             (subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                 (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                 (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
                 (subst id
                  (sym
                   (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                    (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                    (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                  e)
                 [ exp w ]E)
                ⇓ v₁
           ≡⟨ cong (_⇓ v₁) (cong (_[ exp w ]E) (subst₂-∘ id (λ t₁ → Expr [] (t₁ ◁ ∅)) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))) _)) ⟩
             (subst id
                 (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                  (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                  (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                 (subst id
                  (sym
                   (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                    (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                    (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                  e)
                 [ exp w ]E)
                ⇓ v₁
           ≡⟨ cong (λ H → H [ exp w ]E ⇓ v₁)
              (subst-subst-sym {P = id} (cong₂ (λ t₁ → Expr [] (t₁ ◁ ∅))
                  (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                  (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) {p = e}) ⟩
             (e [ exp w ]E) ⇓ v₁
           ∎)
         ------------------------------
           (begin
             𝓥⟦ T₂ ⟧ (Tren-act τ* ρ)
               (subst id
                (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁)
               (z
                (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                 z₁))
           ≡⟨ LRVren-eq′ T₂ ρ τ* (subst id
       (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁) (z
       (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
        z₁)) ⟩
             subst₂ (λ vv zz → Value vv → zz → Set _)
               (assoc-sub-ren T₂ τ* (subst←RE ρ))
               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)
               (𝓥⟦ Tren τ* T₂ ⟧ ρ)
               (subst id
                (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁)
               (z
                (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                 z₁))
           ≡⟨ cong (λ H → H (subst id
                (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁)
               (z
                (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                 z₁))) (subst₂-∘₁ (λ vv zz → vv → zz → Set _) Value
                          (assoc-sub-ren T₂ τ* (subst←RE ρ))
                          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂) (𝓥⟦ Tren τ* T₂ ⟧ ρ)) ⟩
             subst₂ (λ vv zz → vv → zz → Set _)
               (cong Value (assoc-sub-ren T₂ τ* (subst←RE ρ)))
               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)
               (𝓥⟦ Tren τ* T₂ ⟧ ρ)
               (subst id
                (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁)
               (z
                (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                 z₁))
           ≡⟨ cong (λ H → H (subst id
                (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁)
               (z
                (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                 z₁))) (eta-subst₂ (𝓥⟦ Tren τ* T₂ ⟧ ρ) (cong Value (assoc-sub-ren T₂ τ* (subst←RE ρ)))
               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂) ) ⟩
             𝓥⟦ Tren τ* T₂ ⟧ ρ
               (subst id (sym (cong Value (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                (subst id
                 (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁))
               (subst id
                (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
                (z
                 (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                  z₁)))
           ≡⟨ cong (λ H →  𝓥⟦ Tren τ* T₂ ⟧ ρ H
               (subst id
                (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
                (z
                 (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                  z₁)))) (cong (λ H → subst id H
      (subst id
       (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁)) (sym-cong {f = Value} (assoc-sub-ren T₂ τ* (subst←RE ρ)) )) ⟩
             𝓥⟦ Tren τ* T₂ ⟧ ρ
               (subst id (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                (subst id
                 (sym (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))) v₁))
               (subst id
                (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
                (z
                 (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                  z₁)))
           ≡⟨ cong (λ H →  𝓥⟦ Tren τ* T₂ ⟧ ρ H
               (subst id
                (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
                (z
                 (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                  z₁)))) (subst-subst-sym {P = id} (cong Value (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))) {p = v₁}) ⟩
             𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
               (subst id
                (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
                (z
                 (subst id (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                  z₁)))
           ≡⟨ cong (𝓥⟦ Tren τ* T₂ ⟧ ρ v₁)
                   (subst-cong₂ (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                                (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂) z z₁) ⟩
             𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
               (subst id
                (cong₂ (λ A₁ A₂ → A₁ → A₂)
                 (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁))
                 (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
                z z₁)
           ≡˘⟨ cong (λ H → 𝓥⟦ Tren τ* T₂ ⟧ ρ v₁ (subst id H z z₁))
                    (sym-cong₂ (λ A₁ A₂ → A₁ → A₂)
                               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)) ⟩
             𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
               (subst id
                (sym
                 (cong₂ (λ A₁ A₂ → A₁ → A₂)
                  (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                  (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
                z z₁)
           ∎)))
         ------------------------------
         ⟩
          Σ (Value (Tsub (subst←RE ρ) (Tren τ* T₂)))
       (λ v₁ →
          (e [ exp w ]E) ⇓ v₁ ∧
          𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
          (subst id
           (sym
            (cong₂ (λ A₁ A₂ → A₁ → A₂)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
           z z₁))
          ∎)
          ----------------------------------------
      ⟩
      (𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
       ∃-syntax
       (λ v₁ →
          (e [ exp w ]E) ⇓ v₁ ∧
          𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
          (subst id
           (sym
            (cong₂ (λ A₁ A₂ → A₁ → A₂)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
           z z₁))) ∎)
       ⟩
       -- 
         ((z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
          𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
       ∃-syntax
       (λ v₁ →
          (e [ exp w ]E) ⇓ v₁ ∧
          𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
          (subst id
           (sym
            (cong₂ (λ A₁ A₂ → A₁ → A₂)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
           z z₁)))
       ∎)
     ⟩
      ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
       (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
       𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
       ∃-syntax
       (λ v₁ →
          (e [ exp w ]E) ⇓ v₁ ∧
          𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
          (subst id
           (sym
            (cong₂ (λ A₁ A₂ → A₁ → A₂)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
           z z₁)))
    ∎)
     ------------------------------
     ))
   ⟩
    Σ (Expr [] (Tsub (subst←RE ρ) (Tren τ* T₁) ◁ ∅) (Tsub (subst←RE ρ) (Tren τ* T₂)))
      (λ e →
         (exp
          (subst id
           (sym (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))))
           v)
          ≡ (ƛ e))
         ∧
         ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
          (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
          𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
          ∃-syntax
          (λ v₁ →
             (e [ exp w ]E) ⇓ v₁ ∧
             𝓥⟦ Tren τ* T₂ ⟧ ρ v₁
             (subst id
              (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂)))
              z z₁))))
  ≡⟨⟩
    𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ
      (subst id
       (sym (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) v)
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂)))
       z)
  ≡⟨ cong (λ H → H z) (app-subst (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ
       (subst id
        (sym (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) v))
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))) ⟩
    subst (λ Z → Z → Set _)
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
      (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ
       (subst id
        (sym (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) v))
      z
  ≡⟨  cong (λ H → H v z) (app-subst (λ v₁ →
         subst (λ Z → Z → Set _)
         (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
         (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ v₁))
         (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) ⟩
    subst
      (λ v₁ →
         v₁ →
         ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
         Set _)
      (cong Value (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))
      (λ v₁ →
         subst (λ Z → Z → Set _)
         (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
         (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ v₁))
      v z
  ≡˘⟨ cong (λ H → H v z) (subst-∘ {P = (λ v₁ →
         v₁ →
         ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
         Set _)} {f = Value} (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) ⟩
    subst
      (λ v₁ →
         Value v₁ →
         ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
         Set _)
      (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))
      (λ v₁ →
         subst (λ Z → Z → Set _)
         (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
         (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ v₁))
      v z
  ≡˘⟨ cong (λ H → subst
      (λ v₁ →
         Value v₁ →
         ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
         Set _)
      (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))
      H v z) (eta-subst (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ)
                 (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂)) ) ⟩
    subst
      (λ v₁ →
         Value v₁ →
         ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
         Set _)
      (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))
      (subst
       (λ zz →
          Value (Tsub (subst←RE ρ) (Tren τ* (T₁ ⇒ T₂))) → zz → Set _)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
       (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ))
      v z
  ≡˘⟨ cong (λ H → H v z)
           (subst₂-subst-subst (λ vv zz → Value vv → zz → Set _)
                           (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))
                           (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
                           (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ)) ⟩
    subst₂ (λ vv zz → Value vv → zz → Set _)
      (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (T₁ ⇒ T₂))
      (𝓥⟦ Tren τ* (T₁ ⇒ T₂) ⟧ ρ) v z
  ∎

LRVren-eq′ (`∀α l , T) ρ τ* v z =
  begin
    𝓥⟦ `∀α l , T ⟧ (Tren-act τ* ρ) v z
  ≡⟨⟩
    Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (τ* ∘ᵣₛ subst←RE ρ) l) T))
      (λ e →
         (exp v ≡ (Λ l ⇒ e)) ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (e [ T′ ]ET) ⇓ v₁ ∧
             𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))))
  ≡⟨ sigma-subst ((λ e →
         (exp v ≡ (Λ l ⇒ e)) ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (e [ T′ ]ET) ⇓ v₁ ∧
             𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))))) (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) ⟩
    Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (subst←RE ρ) l) (Tren (Tliftᵣ τ* l) T)))
      (λ a′ →
         (exp v ≡
          (Λ l ⇒
           subst id
           (sym
            (sym
             (cong (Expr (l ∷ []) (l ◁* ∅))
              (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
           a′))
         ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (subst id
              (sym
               (sym
                (cong (Expr (l ∷ []) (l ◁* ∅))
                 (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
              a′
              [ T′ ]ET)
             ⇓ v₁
             ∧
             𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))))
  ≡⟨ cong (Σ _) (fun-ext (λ e →
    begin
      (exp v ≡
         (Λ l ⇒
          subst id
          (sym
           (sym
            (cong (Expr (l ∷ []) (l ◁* ∅))
             (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
          e))
        ∧
        ((T′ : Type [] l) (R : REL T′) →
         ∃-syntax
         (λ v₁ →
            (subst id
             (sym
              (sym
               (cong (Expr (l ∷ []) (l ◁* ∅))
                (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
             e
             [ T′ ]ET)
            ⇓ v₁
            ∧
            𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
            (subst Value (lemma1 (Tren-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ []))))
    ≡⟨ cong₂ _∧_
    ----------------------------------------
    (begin
      exp v ≡
        (Λ l ⇒
         subst id
         (sym
          (sym
           (cong (Expr (l ∷ []) (l ◁* ∅))
            (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
         e)
    ≡⟨ cong (λ H → exp v ≡ (Λ l ⇒ subst id (sym H) e))
            (sym-cong {f = (Expr (l ∷ []) (l ◁* ∅))} (assoc-sub↑-ren↑ T τ* (subst←RE ρ)) ) ⟩
      exp v ≡
        (Λ l ⇒
         subst id
         (sym
          (cong (Expr (l ∷ []) (l ◁* ∅))
           (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
         e)
    ≡⟨ cong (λ H → exp v ≡ (Λ l ⇒ subst id H e))
            (sym-cong  {f = (Expr (l ∷ []) (l ◁* ∅))} (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) ⟩
      exp v ≡
        (Λ l ⇒
         subst id
         (cong (Expr (l ∷ []) (l ◁* ∅))
          (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
         e)
    ≡˘⟨ cong (λ H → exp v ≡ (Λ l ⇒ H))
        (subst-∘ {P = id} {f = (Expr (l ∷ []) (l ◁* ∅))} (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) {e} ) ⟩
      exp v ≡
        (Λ l ⇒
         subst (id ∘ Expr (l ∷ []) (l ◁* ∅))
         (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) e)
    ≡˘⟨ cong (λ H → exp v ≡ H)
             (subst-split-Λ (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) e) ⟩
      exp v ≡
        subst CExpr (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))
        (Λ l ⇒ e)
    ≡⟨ subst-swap-eq′ {F = CExpr} (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) (exp v) (Λ l ⇒ e)  ⟩
      subst CExpr
        (sym (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) (exp v)
        ≡ (Λ l ⇒ e)
    ≡˘⟨ cong (_≡ Λ l ⇒ e) ( dist-subst' {F = Value} {G = CExpr} id exp (sym (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) (sym (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) v) ⟩
      exp (subst Value (sym (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) v)
        ≡ (Λ l ⇒ e)
    ≡⟨ cong (λ H → exp H ≡ (Λ l ⇒ e))
             (subst-∘ {P = id} {f = Value} (sym (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))) {v} ) ⟩
      exp (subst id (cong Value (sym (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) v)
        ≡ (Λ l ⇒ e)
    ≡˘⟨ cong (λ H → exp (subst id H v) ≡ (Λ l ⇒ e))
             (sym-cong {f = Value} (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) ) ⟩
      exp (subst id (sym (cong Value (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) v)
        ≡ (Λ l ⇒ e)
    ∎)
    ----------------------------------------
    (dep-ext (λ T′ → dep-ext (λ R →
    begin
      Σ (Value (Tsub (Tliftₛ (τ* ∘ᵣₛ subst←RE ρ) l) T [ T′ ]T))
        (λ v₁ →
           (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
           ⇓ v₁
           ∧
           𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))
    ≡⟨ sigma-subst
         (λ v₁ →
            (subst id
             (sym
              (sym
               (cong (Expr (l ∷ []) (l ◁* ∅))
                (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
             e
             [ T′ ]ET)
            ⇓ v₁
            ∧
            𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
            (subst Value (lemma1 (Tren-act τ* ρ) T T′ R) v₁) (z (⟦ T′ ⟧ [])))
         (cong Value (cong (λ T₀ → T₀ [ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) ⟩
      Σ (Value (Tsub (Tliftₛ (subst←RE ρ) l) (Tren (Tliftᵣ τ* l) T) [ T′ ]T))
        (λ v₁ →
           (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
           ⇓
           subst id (sym (cong Value (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
           v₁
           ∧
           𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
            (subst id (sym (cong Value (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
             v₁))
           (z (⟦ T′ ⟧ [])))
    ≡⟨ cong (Σ _) (fun-ext (λ v₁ →
      cong₂ _∧_
      --------------------------------------------------
      (begin
        (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
          ⇓
          subst id (sym (cong Value (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))) v₁
      ≡⟨ cong ((subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET ) ⇓_)
         (cong (λ H → subst id H v₁) (sym-cong {f = Value} (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
       ⟩
        (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
          ⇓
          subst id (cong Value (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))) v₁
      ≡⟨ cong ((subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET ) ⇓_)
             (cong (λ H → subst id (cong Value H) v₁)
             (sym-cong {f = (_[ T′ ]T)} (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) ⟩
        (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
          ⇓
          subst id (cong Value (cong (_[ T′ ]T) (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))) v₁
      ≡˘⟨ cong ((subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET ) ⇓_)
              (subst-∘ {P = id}{f = Value} (cong (_[ T′ ]T) (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) {v₁} ) ⟩
        (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
          ⇓
          subst Value (cong (_[ T′ ]T) (sym (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) v₁
      ≡⟨ cong ((subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET ) ⇓_)
             (cong (λ H → subst Value (cong (_[ T′ ]T) H) v₁)
               (sym-sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)) )) ⟩
        (subst id (sym (sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) e [ T′ ]ET)
          ⇓
          subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁
      ≡⟨ cong (_⇓ subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁)
              (cong (λ H → (subst id H e [ T′ ]ET)) (sym-sym (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) )) ⟩
        (subst id (cong (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) e [ T′ ]ET)
          ⇓
          subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁
      ≡˘⟨ cong (_⇓ subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁)
               (cong (_[ T′ ]ET) (subst-∘ {P = id}{f = (Expr (l ∷ []) (l ◁* ∅))} (assoc-sub↑-ren↑ T τ* (subst←RE ρ)) {e} )) ⟩
        (subst (Expr (l ∷ []) (l ◁* ∅)) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)) e [ T′ ]ET)
          ⇓
          subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁
      ≡⟨ cong (_⇓ subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁)
              ( dist-subst' {F = (Expr (l ∷ []) (l ◁* ∅))} {G = CExpr} (_[ T′ ]T) (_[ T′ ]ET) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)) (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) e ) ⟩
        subst CExpr (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) (e [ T′ ]ET)
          ⇓
          subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁
      ≡⟨  subst-split-eq-⇓ (e [ T′ ]ET) (subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) v₁) (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) ⟩
        (e [ T′ ]ET) ⇓
          subst Value (sym (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))
          (subst Value (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))
           v₁)
      ≡⟨ cong ((e [ T′ ]ET) ⇓_) (subst-sym-subst {P = Value} (cong (_[ T′ ]T) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))) {v₁}) ⟩
        (e [ T′ ]ET) ⇓ v₁
      ∎)
      --------------------------------------------------
      (begin
        𝓥⟦ T ⟧ (REext (Tren-act τ* ρ) (T′ , R))
          (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
           (subst id (sym (cong Value (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))) v₁))
          (z (⟦ T′ ⟧ []))
      ≡⟨ cong (λ K → K (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
           (subst id (sym (cong Value (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))) v₁))
          (z (⟦ T′ ⟧ []))) (dcongωl 𝓥⟦ T ⟧ (Tren-act-REext ρ τ* T′ R)) ⟩
        substω (λ z₁ → Value (Tsub (subst←RE z₁) T) → ⟦ T ⟧ (subst-to-env* (subst←RE z₁) []) → Set _)
          (symω (Tren-act-REext ρ τ* T′ R))
          (𝓥⟦ T ⟧ (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R))))
          (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
           (subst id
            (sym
             (cong Value
              (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
            v₁))
          (z (⟦ T′ ⟧ []))
      ≡⟨ cong (λ K → K 
          (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
           (subst id
            (sym
             (cong Value
              (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
            v₁))
          (z (⟦ T′ ⟧ []))) (substω-congω (λ z₁ → Value (Tsub z₁ T) → ⟦ T ⟧ (subst-to-env* z₁ []) → Set _) subst←RE (symω (Tren-act-REext ρ τ* T′ R)) (𝓥⟦ T ⟧ (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))) )
       ⟩
        subst
          (λ z₁ → Value (Tsub z₁ T) → ⟦ T ⟧ (subst-to-env* z₁ []) → Set _)
          (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))
          (𝓥⟦ T ⟧ (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R))))
          (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
           (subst id
            (sym
             (cong Value
              (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
            v₁))
          (z (⟦ T′ ⟧ []))
      ≡⟨ cong (λ K → K 
          (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
           (subst id
            (sym
             (cong Value
              (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
            v₁))
          (z (⟦ T′ ⟧ []))) (subst-fun (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))) (𝓥⟦ T ⟧ (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))))
       ⟩
        𝓥⟦ T ⟧ (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))
          (subst (λ z₁ → Value (Tsub z₁ T))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
            (subst id
             (sym
              (cong Value
               (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
             v₁)))
          (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (z (⟦ T′ ⟧ [])))
      ≡⟨ LRVren-eq′ T (REext ρ (T′ , R)) (Tliftᵣ τ* l) _ _  ⟩
        subst₂ (λ vv zz → Value vv → zz → Set _)
          (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))
          (Tren*-preserves-semantics
           (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)
          (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R)))
          (subst (λ z₁ → Value (Tsub z₁ T))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
            (subst id
             (sym
              (cong Value
               (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
             v₁)))
          (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (z (⟦ T′ ⟧ [])))
      ≡⟨ cong (λ K → K 
          (subst (λ z₁ → Value (Tsub z₁ T))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
            (subst id
             (sym
              (cong Value
               (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
             v₁)))
          (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (z (⟦ T′ ⟧ [])))) (subst₂-subst-subst (λ vv zz → Value vv → zz → Set _)
                                      (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))
                                      (Tren*-preserves-semantics (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)
                                      (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R)))) ⟩
        subst
          (λ v₂ → Value v₂ → ⟦ T ⟧ (subst-to-env* (subst←RE (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))) []) → Set _)
          (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))
          (subst
           (λ zz → Value (Tsub (subst←RE (REext ρ (T′ , R))) (Tren (Tliftᵣ τ* l) T)) → zz → Set _)
           (Tren*-preserves-semantics (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)
           (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R))))
          (subst (λ z₁ → Value (Tsub z₁ T))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
            (subst id
             (sym
              (cong Value
               (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
             v₁)))
          (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (z (⟦ T′ ⟧ [])))
      ≡⟨ cong (λ K → K 
          (subst (λ z₁ → Value (Tsub z₁ T))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
            (subst id
             (sym
              (cong Value
               (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
             v₁)))
          (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
           (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
           (z (⟦ T′ ⟧ [])))) ((subst-fun (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) (subst
                        (λ zz →
                           Value (Tsub (subst←RE (REext ρ (T′ , R))) (Tren (Tliftᵣ τ* l) T)) →
                           zz → Set _)
                        (Tren*-preserves-semantics
                         (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)
                        (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R)))) )) ⟩
        subst
          (λ zz →
             Value (Tsub (subst←RE (REext ρ (T′ , R))) (Tren (Tliftᵣ τ* l) T)) →
             zz → Set _)
          (Tren*-preserves-semantics
           (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)
          (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R)))
          (subst (λ v₂ → Value v₂)
           (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
           (subst (λ z₁ → Value (Tsub z₁ T))
            (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
            (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
             (subst id
              (sym
               (cong Value
                (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
              v₁))))
          (subst
           (λ v₂ →
              ⟦ T ⟧
              (subst-to-env*
               (subst←RE (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))) []))
           (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
           (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
            (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
            (z (⟦ T′ ⟧ []))))
      ≡⟨ cong (λ K → K 
          (subst (λ v₂ → Value v₂)
           (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
           (subst (λ z₁ → Value (Tsub z₁ T))
            (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
            (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
             (subst id
              (sym
               (cong Value
                (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
              v₁))))
          (subst
           (λ v₂ →
              ⟦ T ⟧
              (subst-to-env*
               (subst←RE (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))) []))
           (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
           (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
            (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
            (z (⟦ T′ ⟧ []))))) (subst-fun (Tren*-preserves-semantics (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T) (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R)))) ⟩
        𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R))
          (subst
           (λ v₂ →
              Value (Tsub (subst←RE (REext ρ (T′ , R))) (Tren (Tliftᵣ τ* l) T)))
           (sym
            (Tren*-preserves-semantics
             (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
           (subst (λ v₂ → Value v₂)
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst (λ z₁ → Value (Tsub z₁ T))
             (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst id
               (sym
                (cong Value
                 (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
               v₁)))))
          (subst (λ v₂ → v₂)
           (sym
            (Tren*-preserves-semantics
             (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
           (subst
            (λ v₂ →
               ⟦ T ⟧
               (subst-to-env*
                (subst←RE (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))) []))
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
             (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
             (z (⟦ T′ ⟧ [])))))
      ≡⟨ cong₂ (𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R)))
      ----------------------------------------
        (begin
          subst
            (λ v₂ →
               Value (Tsub (subst←RE (REext ρ (T′ , R))) (Tren (Tliftᵣ τ* l) T)))
            (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
            (subst (λ v₂ → Value v₂)
             (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
             (subst (λ z₁ → Value (Tsub z₁ T))
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
              (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
               (subst id
                (sym
                 (cong Value
                  (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
                v₁))))
        ≡⟨ subst-const (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)) ⟩
          subst Value
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst (λ z₁ → Value (Tsub z₁ T))
             (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst id
               (sym
                (cong Value
                 (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
               v₁)))
        ≡⟨ cong (subst Value (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))))
            (subst-∘ {P = Value}{f = λ z₁ → Tsub z₁ T} (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))) {(subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst id
               (sym
                (cong Value
                 (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
               v₁))} ) ⟩
          subst Value
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst Value
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst id
               (sym
                (cong Value
                 (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
               v₁)))
        ≡⟨ cong (λ H → subst Value
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst Value
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst id H v₁)))) (sym-cong {f = Value} (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) ⟩
          subst Value
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst Value
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst id
               (cong Value
                (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))))
               v₁)))
        ≡˘⟨ cong (λ H → subst Value
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst Value
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              H))) (subst-∘ {P = id}{f = Value} (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) {v₁}) ⟩
          subst Value
            (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
            (subst Value
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
              (subst Value
               (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
               v₁)))
        ≡⟨ subst-subst {P = Value} (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))) {(sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))} ⟩
          subst Value
            (trans
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (sym
              (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))))
            (subst Value (lemma1 (Tren-act τ* ρ) T T′ R)
             (subst Value
              (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
              v₁))
        ≡⟨ subst-subst {P = Value} (lemma1 (Tren-act τ* ρ) T T′ R) {(trans
             (cong (λ z₁ → Tsub z₁ T)
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (sym
              (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))))}  ⟩
          subst Value
            (trans (lemma1 (Tren-act τ* ρ) T T′ R)
             (trans
              (cong (λ z₁ → Tsub z₁ T)
               (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
              (sym
               (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))))
            (subst Value
             (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
             v₁)
        ≡⟨ subst-subst {P = Value} (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) {(trans (lemma1 (Tren-act τ* ρ) T T′ R)
             (trans
              (cong (λ z₁ → Tsub z₁ T)
               (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
              (sym
               (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))))}  ⟩
          subst Value
            (trans
             (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
             (trans (lemma1 (Tren-act τ* ρ) T T′ R)
              (trans
               (cong (λ z₁ → Tsub z₁ T)
                (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
               (sym
                (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))))))
            v₁
        ≡⟨ subst-irrelevant (trans
             (sym (cong (_[ T′ ]T) (sym (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
             (trans (lemma1 (Tren-act τ* ρ) T T′ R)
              (trans
               (cong (λ z₁ → Tsub z₁ T)
                (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
               (sym
                (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))))))  (lemma1 ρ (Tren (Tliftᵣ τ* l) T) T′ R) v₁ ⟩
          subst Value (lemma1 ρ (Tren (Tliftᵣ τ* l) T) T′ R) v₁
        ∎)
      ----------------------------------------
        (begin
          subst id
            (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
            (subst (λ v₂ → ⟦ T ⟧ (subst-to-env* (subst←RE (Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)))) []))
             (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))))
             (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
              (z (⟦ T′ ⟧ []))))
        ≡⟨ cong (subst id (sym (Tren*-preserves-semantics (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)))
           (subst-const (sym (assoc-sub-ren T (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R))))) ) ⟩
          subst id
            (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
            (subst (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
             (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R))))
             (z (⟦ T′ ⟧ [])))
        ≡⟨ cong (subst id (sym (Tren*-preserves-semantics (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)))
           (subst-∘ {P = id} {f = (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))}
                     (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))) {z (⟦ T′ ⟧ [])}) ⟩
          subst id
            (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
            (subst id
             (cong (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (z (⟦ T′ ⟧ [])))
        ≡⟨ subst-subst {P = id}
             (cong (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             {(sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))}
              {z (⟦ T′ ⟧ [])} ⟩
          subst id
            (trans
             (cong (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (sym
              (Tren*-preserves-semantics
               (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)))
            (z (⟦ T′ ⟧ []))
        ≡⟨ subst-irrelevant {F = id}
            (trans
             (cong (λ z₁ → ⟦ T ⟧ (subst-to-env* z₁ []))
              (sym (congωl subst←RE (symω (Tren-act-REext ρ τ* T′ R)))))
             (sym
              (Tren*-preserves-semantics
               (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T)))
            (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
            (z (⟦ T′ ⟧ [])) ⟩
          subst id
            (sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))
            (z (⟦ T′ ⟧ []))
        ≡˘⟨ dist-subst*-sym {F = id}{G = id}  (λ z → z (⟦ T′ ⟧ [])) (λ z → z (⟦ T′ ⟧ []))
            (λ { α → Tren*-preserves-semantics (Tren*-lift α (τ*∈Ren* τ* (subst←RE ρ))) T})
            ((sym
             (Tren*-preserves-semantics
              (τ*∈Ren* (Tliftᵣ τ* l) (subst←RE (REext ρ (T′ , R)))) T))) z  ⟩
          subst id
            (sym
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T)))
            z (⟦ T′ ⟧ [])
        ∎)
      ----------------------------------------
       ⟩
        𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R))
          (subst Value (lemma1 ρ (Tren (Tliftᵣ τ* l) T) T′ R) v₁)
          (subst id (sym (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T)))
           z (⟦ T′ ⟧ []))
      ∎)
      --------------------------------------------------
      ))
     ⟩
      Σ (Value (Tsub (Tliftₛ (subst←RE ρ) l) (Tren (Tliftᵣ τ* l) T) [ T′ ]T))
        (λ v₁ →
           (e [ T′ ]ET) ⇓ v₁ ∧
           𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R))
           (subst Value (lemma1 ρ (Tren (Tliftᵣ τ* l) T) T′ R) v₁)
           (subst id
            (sym
             (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T)))
            z (⟦ T′ ⟧ [])))
    ∎
    )))
    ----------------------------------------
    ⟩
      (exp
         (subst id
          (sym
           (cong Value (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ)))))
          v)
         ≡ (Λ l ⇒ e))
        ∧
        ((T′ : Type [] l) (R : REL T′) →
         ∃-syntax
         (λ v₁ →
            (e [ T′ ]ET) ⇓ v₁ ∧
            𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R))
            (subst Value (lemma1 ρ (Tren (Tliftᵣ τ* l) T) T′ R) v₁)
            (subst id
             (sym
              (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T)))
             z (⟦ T′ ⟧ []))))
    ∎))
  ⟩
    Σ (Expr (l ∷ []) (l ◁* ∅) (Tsub (Tliftₛ (subst←RE ρ) l) (Tren (Tliftᵣ τ* l) T)))
      (λ e → (exp (subst id (sym (cong Value (cong (`∀α_,_ l) (assoc-sub↑-ren↑ T τ* (subst←RE ρ))))) v) ≡ (Λ l ⇒ e))
         ∧
         ((T′ : Type [] l) (R : REL T′) →
          ∃-syntax
          (λ v₁ →
             (e [ T′ ]ET) ⇓ v₁ ∧
             𝓥⟦ Tren (Tliftᵣ τ* l) T ⟧ (REext ρ (T′ , R))
             (subst Value (lemma1 ρ (Tren (Tliftᵣ τ* l) T) T′ R) v₁)
             (subst id
              (sym
               (dep-ext
                (λ { α → Tren*-preserves-semantics
                         {ρ* = Tliftᵣ τ* l}
                         {η₁ = α ∷ subst-to-env* (subst←RE (Tren-act τ* ρ)) []}
                         {η₂ = α ∷ (subst-to-env* (subst←RE ρ) [])}
                         (Tren*-lift α (τ*∈Ren* τ* (subst←RE ρ))) T
                   })))
              z (⟦ T′ ⟧ [])))))
  ≡⟨⟩
    𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ
      (subst id
       (sym (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))) v)
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T)))
       z)
  ≡⟨ cong (λ H → H z)
    (app-subst 
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ
       (subst id
        (sym (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))) v))
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))) ⟩
    subst (λ Z → Z → Set _)
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ
       (subst id
        (sym (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))) v))
      z
  ≡˘⟨ cong (λ H → H 
      (subst id
       (sym (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))) v)
      z)
      (eta-subst (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ) (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T)) ) ⟩
    subst
      (λ zz → Value (Tsub (subst←RE ρ) (Tren τ* (`∀α l , T))) → zz → Set _)
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ)
      (subst id
       (sym (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))) v)
      z
  ≡⟨ cong (λ H → H v z)
    (app-subst (subst
       (λ zz →
          Value (Tsub (subst←RE ρ) (Tren τ* (`∀α l , T))) →
          zz → Set _)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
       (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ))
       (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))) ⟩
    subst
      (λ v₁ → v₁ → ⟦ `∀α l , T ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) → Set _)
      (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))
      (subst
       (λ zz →
          Value (Tsub (subst←RE ρ) (Tren τ* (`∀α l , T))) →
          zz → Set _)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
       (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ))
      v z
  ≡˘⟨ cong (λ H → H v z)
      (subst₂-subst-subst (λ vv zz → vv → zz → Set _)
      (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ)) ⟩
    subst₂ (λ vv zz → vv → zz → Set _)
      (cong Value (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ)))
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ) v z
  ≡˘⟨ cong (λ H → H v z)
      (subst₂-∘₁ (λ vv zz → vv → zz → Set _) Value
      (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ))
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ)) ⟩
    subst₂ (λ vv zz → Value vv → zz → Set _)
      (assoc-sub-ren (`∀α l , T) τ* (subst←RE ρ))
      (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) (`∀α l , T))
      (𝓥⟦ Tren τ* (`∀α l , T) ⟧ ρ) v z
  ∎

LRVren-eq :  ∀ {Δ₁}{Δ₂}{l}
  → (T : Type Δ₁ l)
  → (ρ : RelEnv Δ₂)
  → (τ* : TRen Δ₁ Δ₂)
  → let σ* = subst←RE ρ
  in 𝓥⟦ T ⟧ (Tren-act τ* ρ) ≡
    subst₂ (λ vv zz → Value vv → zz → Set l)
           (assoc-sub-ren T τ* σ*)
           (Tren*-preserves-semantics {ρ* = τ*}{subst-to-env* (subst←RE (Tren-act τ* ρ)) []}{subst-to-env* σ* []} (τ*∈Ren* τ* σ*) T)
           (𝓥⟦ Tren τ* T ⟧ ρ)
LRVren-eq T ρ τ* = fun-ext (λ v → fun-ext (λ z → LRVren-eq′ T ρ τ* v z))

LRVwk-eq : ∀ {Δ}{l}{l₁}
  → (T : Type Δ l)
  → (ρ : RelEnv (l₁ ∷ Δ))
  → let σ* = subst←RE ρ
  in (v : Value (Tsub (Tdropₛ σ*) T))
  → (z : ⟦ T ⟧ (subst-to-env* (Tdropₛ σ*) []))
  → 𝓥⟦ T ⟧ (REdrop ρ) v z
  ≡ 𝓥⟦ Twk T ⟧
        ρ
        (subst Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) v)
        (subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T)) z)
LRVwk-eq T ρ v z =
  begin
    𝓥⟦ T ⟧ (REdrop ρ) v z
  ≡⟨ LRVren-eq′ T ρ (Twkᵣ Tidᵣ) v z ⟩
    subst₂ (λ vv zz → Value vv → zz → Set _)
      (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))
      (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)
      (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ) v z
  ≡⟨ cong (λ K → K v z) (subst₂-∘₁ (λ vv zz → vv → zz → Set _) Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)) (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T) (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ)) ⟩
    subst₂ (λ vv zz → vv → zz → Set _)
      (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))
      (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)
      (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ) v z
  ≡⟨ cong (λ K → K v z) (subst₂-subst-subst (λ vv zz → vv → zz → Set _) (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T) (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ)) ⟩
    subst
      (λ v₁ →
         v₁ → ⟦ T ⟧ (subst-to-env* (Tdropₛ (subst←RE ρ)) []) → Set _)
      (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))
      (subst
       (λ zz →
          Value (Tsub (subst←RE ρ) (Tren (Twkᵣ Tidᵣ) T)) → zz → Set _)
       (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)
       (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ))
      v z
  ≡⟨ cong (λ K → subst
      (λ v₁ →
         v₁ → ⟦ T ⟧ (subst-to-env* (Tdropₛ (subst←RE ρ)) []) → Set _)
      (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))
      K v z)
    (eta-subst (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ) (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T) ) ⟩
    subst
      (λ v₁ →
         v₁ → ⟦ T ⟧ (subst-to-env* (Tdropₛ (subst←RE ρ)) []) → Set _)
      (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))
      (λ v₁ →
         subst (λ Z → Z → Set _)
         (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)
         (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ v₁))
      v z
  ≡˘⟨ cong (λ K → K v z) (app-subst (λ v₁ →
         subst (λ Z → Z → Set _)
         (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)
         (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ v₁))
         (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))) ⟩
    subst (λ Z → Z → Set _)
      (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)
      (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
       (subst id
        (sym (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))) v))
      z
  ≡˘⟨ cong (λ K → K z) (app-subst (𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
       (subst id
        (sym (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))) v))
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T)) ⟩
    𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
      (subst id
       (sym (cong Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))) v)
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T))
       z)
  ≡⟨ cong (λ K → 𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
      (subst id K v)
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T))
       z))
     (sym-cong {f = Value} (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) ⟩
    𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
      (subst id
       (cong Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))) v)
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T))
       z)
  ≡˘⟨ cong (λ K → 𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
      K
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T))
       z))
    (subst-∘ {P = id} {f = Value} (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))) ⟩
    𝓥⟦ Tren (Twkᵣ Tidᵣ) T ⟧ ρ
      (subst (id ∘ Value)
       (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) v)
      (subst id
       (sym
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T))
       z)
  ≡⟨ cong
       (𝓥⟦ Twk T ⟧ ρ
        (subst Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) v))
       (subst-irrelevant {F = id} (sym
        (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) (subst←RE ρ)) T))
        (sym
        (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T)) z) ⟩
    𝓥⟦ Twk T ⟧ ρ
      (subst Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) v)
      (subst id
       (sym
        (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T))
       z)
  ∎

--! MCGLookupType
𝓖-lookup : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T : Type Δ l)
  → 𝓖⟦_⟧ Γ ρ χ γ
  → (x : inn T Γ)
  → 𝓥⟦ T ⟧ ρ (χ l _ x) (γ l T x)

𝓖-lookup .(T ◁ _) ρ χ γ T (𝓥 , 𝓖) here = 𝓥
𝓖-lookup (_ ◁ Γ) ρ χ γ T (𝓥 , 𝓖) (there x) = 𝓖-lookup Γ ρ (Cdrop χ) (ENVdrop Γ _ γ) T 𝓖 x
𝓖-lookup (_ ◁* Γ) ρ χ γ .(Twk _) 𝓖 (tskip {T = T} x) =
  let ih = 𝓖-lookup Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ) T 𝓖 x in
  let v = χ _ (Twk T) (tskip x) in
  let z = γ _ (Twk T) (tskip x) in
  let eq = LRVwk-eq T ρ (subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)) v) (subst id (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T) z) in
  subst id (begin
    𝓥⟦ T ⟧ (REdrop ρ) (Cdropt χ _ T x) (Gdropt (subst←RE ρ) γ _ T x)
  ≡⟨ refl ⟩
    𝓥⟦ T ⟧ (REdrop ρ)
      (subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)) v)
      (subst id
       (Tren*-preserves-semantics
        (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
         (⟦ subst←RE ρ _ here ⟧ []))
        T)
       z)
  ≡⟨ eq ⟩
    𝓥⟦ Twk T ⟧ ρ
      (subst Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))
       (subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)) v))
      (subst id
       (sym
        (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T))
       (subst id
        (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T)
        z))
  ≡⟨ cong (λ K → 𝓥⟦ Twk T ⟧ ρ
      K
      (subst id
       (sym
        (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T))
       (subst id
        (Tren*-preserves-semantics
         (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
          (⟦ subst←RE ρ _ here ⟧ []))
         T)
        z))) (subst-sym-subst (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)) {v}) ⟩
    𝓥⟦ Twk T ⟧ ρ v
      (subst id
       (sym
        (Tren*-preserves-semantics
         (λ v₁ →
            wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
            (⟦ subst←RE ρ _ here ⟧ []) v₁)
         T))
       (subst id
        (Tren*-preserves-semantics
         (λ v₁ →
            wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
            (⟦ subst←RE ρ _ here ⟧ []) v₁)
         T)
        z))
  ≡⟨ cong (𝓥⟦ Twk T ⟧ ρ v)
          (subst-sym-subst (Tren*-preserves-semantics
         (λ v₁ →
            wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
            (⟦ subst←RE ρ _ here ⟧ []) v₁)
         T) {z}) ⟩
    𝓥⟦ Twk T ⟧ ρ v z
  ∎) ih 


Cextend-Elift : ∀ {σ* : TSub Δ []} {Γ : TEnv Δ}{l}{T : Type Δ l}{l′}{T′ : Type Δ l′}
  → (χ : CSub σ* Γ)
  → (w : Value (Tsub σ* T))
  → (e : Expr Δ (T ◁ Γ) T′)
  → Csub (Cextend χ w) e ≡ (Esub σ* (Eliftₛ σ* (ES←SC χ)) e [ exp w ]E)
Cextend-Elift {Δ} {σ*} {Γ} {l} {T} {l′} {T′} χ w e =
  begin
    Csub (Cextend χ w) e
  ≡⟨⟩
    Esub σ* (ES←SC (Cextend χ w)) e
  ≡⟨ cong (λ σ → Esub σ* σ e) (Cextend-Eext χ w) ⟩
    Esub σ* (Eextₛ σ* (ES←SC χ) (exp w)) e
  ≡⟨ Eext-Elift {σ* = σ*} (ES←SC χ) (exp w) e ⟩
    Esub σ*
      (subst (λ τ* → ESub τ* (T ◁ Γ) ∅) (TSub-id-right σ*)
       (Eliftₛ σ* (ES←SC χ) >>SS
        sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w))))
      e
  ≡⟨ dist-subst' {F = (λ τ* → ESub τ* (T ◁ Γ) ∅)} {G = Expr [] ∅} 
      (λ σ → Tsub σ T′) (λ {τ*} σ → Esub τ* σ e)
      (TSub-id-right σ*) (cong (λ τ* → Tsub τ* T′) (TSub-id-right σ*))
      (Eliftₛ σ* (ES←SC χ) >>SS
         sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w))) ⟩
    subst (Expr [] ∅) (cong (λ τ* → Tsub τ* T′) (TSub-id-right σ*))
      (Esub (σ* ∘ₛₛ Tidₛ)
       (Eliftₛ σ* (ES←SC χ) >>SS
        sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
       e)
  ≡⟨ subst-irrelevant (cong (λ τ* → Tsub τ* T′) (TSub-id-right σ*)) (trans (sym (assoc-sub-sub T′ σ* Tidₛ)) (TidₛT≡T (Tsub σ* T′))) _ ⟩
    subst (λ v → Expr [] ∅ v)
      (trans (sym (assoc-sub-sub T′ σ* Tidₛ)) (TidₛT≡T (Tsub σ* T′)))
      (Esub (σ* ∘ₛₛ Tidₛ)
       (Eliftₛ σ* (ES←SC χ) >>SS
        sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
       e)
  ≡˘⟨ subst-subst (sym (assoc-sub-sub T′ σ* Tidₛ)) {y≡z = (TidₛT≡T (Tsub σ* T′))} ⟩
    subst (λ v → Expr [] ∅ v) (TidₛT≡T (Tsub σ* T′))
      (subst (λ v → Expr [] ∅ v) (sym (assoc-sub-sub T′ σ* Tidₛ))
       (Esub (σ* ∘ₛₛ Tidₛ)
        (Eliftₛ σ* (ES←SC χ) >>SS
         sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
        e))
  ≡˘⟨ cong (subst (Expr _ _) (TidₛT≡T (Tsub σ* T′)))
     (subst-swap _ _ _ (Eassoc-sub-sub e (Eliftₛ σ* (ES←SC χ)) (Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))))
     ⟩
    subst (Expr [] ∅) (TidₛT≡T (Tsub σ* T′))
      (Esub Tidₛ
       (Eextₛ Tidₛ Eidₛ
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
       (Esub σ* (Eliftₛ σ* (ES←SC χ)) e))
  ≡⟨ refl ⟩
    (Esub σ* (Eliftₛ σ* (ES←SC χ)) e [ exp w ]E)
  ∎


Gdropt-ext≡id : (ρ : RelEnv Δ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T′ : Type [] l) (R : REL T′)
  → (Gdropt (subst←RE (REext ρ (T′ , R))) (extend-tskip γ)) ≡ω γ
Gdropt-ext≡id ρ γ T′ R =
  fun-ext-llω-ω (λ x y z → subst-subst-sym (Tren*-preserves-semantics (λ x₁ → refl) y))

Cdropt-Cextt≡id : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (l : Level) (T′ : Type [] l) (R : REL T′)
  → (Cdropt (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))) ≡ χ
Cdropt-Cextt≡id Γ ρ χ l T′ R =
  let sub₁ = subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) in
  begin
    Cdropt (sub₁ (Cextt χ T′))
  ≡⟨ dist-subst' {F = (λ σ → CSub σ (l ◁* Γ))} {G = id} (λ x → CSub (Tdropₛ x) Γ) Cdropt (sym (subst←RE-ext-ext ρ T′ R)) refl (Cextt χ T′) ⟩ 
    Cdropt (Cextt χ T′)
  ≡⟨ (fun-ext λ x → fun-ext λ y → fun-ext λ z → (elim-subst Value
       (assoc-sub-ren y (λ z₁ x₁ → there x₁) (Textₛ (λ l₁ x₁ → proj₁ (ρ l₁ x₁)) T′))
       (sym
        (trans
         (assoc-sub-ren y (λ z₁ x₁ → there x₁)
          (Textₛ (λ l₁ x₁ → proj₁ (ρ l₁ x₁)) T′))
         (trans
          (sym (assoc-sub-sub y (λ z₁ → `_) (λ l₁ x₁ → proj₁ (ρ l₁ x₁))))
          (trans (cong (Tsub (λ l₁ x₁ → proj₁ (ρ l₁ x₁))) (TidₛT≡T y))
           refl)))) (χ x y z)))
  ⟩
    χ ∎

