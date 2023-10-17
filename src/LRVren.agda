module LRVren where

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
open import SmallStep
open import Logical1

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

LRVren-eq {l = l} (` x) ρ τ* =

  let b₁≡b₂ = τ*∈Ren* τ* (subst←RE ρ) x in

  begin
    (λ v z →
         proj₂ (Tren-act τ* ρ l x) v
         (subst id
          (sym (subst-var-preserves x (subst←RE (Tren-act τ* ρ)) [])) z))
  ≡⟨ fun-ext₂ (λ x₁ y → cong (proj₂ (Tren-act τ* ρ l x) x₁)
                        (trans
                          (subst-irrelevant (sym (subst-var-preserves x (subst←RE (Tren-act τ* ρ)) [])) _ y)
                          (sym (subst-subst {P = id} (sym b₁≡b₂) {y≡z = (sym (subst-var-preserves (τ* l x) (subst←RE ρ) []))})))) ⟩
    (λ v z → proj₂ (Tren-act τ* ρ l x) v 
             (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) []))
               (subst id (sym b₁≡b₂) z)))
  ≡⟨ fun-ext (λ v′ → app-subst (λ z → proj₂ (Tren-act τ* ρ l x) v′ 
                                  (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z)) b₁≡b₂) ⟩
    (λ v →  subst (λ zz → zz → Set l) (τ*∈Ren* τ* (subst←RE ρ) x)
      (λ z → proj₂ (Tren-act τ* ρ l x) v
         (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z)))
  ≡⟨ fun-ext₂ (λ v′ z′ →
              begin
                  subst (λ Z → Z → Set l) (τ*∈Ren* τ* (subst←RE ρ) x)
                    (λ z → proj₂ (Tren-act τ* ρ l x) v′
                                 (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z))
                    z′
              ≡˘⟨ cong (λ H → H v′ z′) 
                    (eta-subst (λ v z →
                       proj₂ (Tren-act τ* ρ l x) v
                       (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z)) (τ*∈Ren* τ* (subst←RE ρ) x))
                ⟩
                subst (λ zz → Value (proj₁ (Tren-act τ* ρ l x)) → zz → Set l)
                    (τ*∈Ren* τ* (subst←RE ρ) x)
                    (λ v z →
                       proj₂ (Tren-act τ* ρ l x) v
                       (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z))
                    v′ z′
              ∎)
  ⟩
    subst (λ zz → Value (proj₁ (Tren-act τ* ρ l x)) → zz → Set l)
      (τ*∈Ren* τ* (subst←RE ρ) x)
      (λ v z →
         proj₂ (Tren-act τ* ρ l x) v
         (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z))

  ≡˘⟨ subst₂→subst (λ vv zz → Value vv → zz → Set l) (τ*∈Ren* τ* (subst←RE ρ) x) (λ v z →
         proj₂ (ρ l (τ* l x)) v
         (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z)) ⟩
      subst₂ (λ vv zz → Value vv → zz → Set l) refl
      (τ*∈Ren* τ* (subst←RE ρ) x)
      (λ v z →
         proj₂ (ρ l (τ* l x)) v
         (subst id (sym (subst-var-preserves (τ* l x) (subst←RE ρ) [])) z))
  ∎
LRVren-eq (T₁ ⇒ T₂) ρ τ* = {!!}
LRVren-eq (`∀α l , T) ρ τ* = {!!}
LRVren-eq `ℕ ρ τ* = refl


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
    (∃[ e ]
         (v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
  ≡⟨ refl ⟩
    Σ (Expr [] (Tsub (subst←RE (Tren-act τ* ρ)) T₁ ◁ ∅) (Tsub (subst←RE (Tren-act τ* ρ)) T₂))
      (λ e → (v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁))))
  ≡⟨ cong (Σ _)
          (fun-ext (λ e →
            let eq≡ = begin
                        (v ≡ (ƛ e))
                          ≡˘⟨ cong (v ≡_) (subst-sym-subst {P = Value} (sym
                              (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                               (assoc-sub-ren T₂ τ* (subst←RE ρ))))) ⟩
                            v ≡
                            subst Value
                            (sym
                             (sym
                              (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                               (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                            (subst (Expr [] ∅)
                             (sym
                              (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                               (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                             (ƛ e))
                          ≡˘⟨ subst-swap-eq {F = Value} (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) v (subst (Expr [] ∅) (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) (ƛ e)) ⟩
                            subst Value (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) v
                            ≡
                            (subst (Expr [] ∅) (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) (ƛ e))
                          ≡⟨ cong (_≡ _) (subst-∘ {P = id}{f = Value} (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) ⟩
                            subst id (cong Value (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) v
                            ≡
                            (subst (Expr [] ∅) (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) (ƛ e))
                          ≡˘⟨ cong (_≡ _) (cong (λ p → subst id p v) (sym-cong {f = Value} (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ)))) ⟩
                            subst id
                             (sym
                              (cong Value
                               (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))))
                             v
                             ≡
                             (subst (Expr [] ∅) (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) (ƛ e))
                          ≡⟨ cong (_ ≡_) (subst-split-ƛ (sym (assoc-sub-ren (T₁ ⇒ T₂) τ* (subst←RE ρ))) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))) e) ⟩
                            (subst id
                             (sym
                              (cong Value
                               (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                                (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                             v
                             ≡
                             (ƛ
                              subst₂
                               (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂)
                                (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                                (sym (assoc-sub-ren T₂ τ* (subst←RE ρ)))
                              e))
                          ≡⟨ cong ((_ ≡_) ∘ ƛ_) (subst₂-∘ id (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂) (sym (assoc-sub-ren T₁ τ* (subst←RE ρ))) (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))) e) ⟩
                            (subst id
                             (sym
                              (cong Value
                               (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                                (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                             v
                             ≡
                             (ƛ
                              subst id
                               (cong₂ (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂)
                                (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))
                                (sym (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                              e))
                          ≡˘⟨ cong ((_ ≡_) ∘ ƛ_ ∘ (λ p → subst id p e)) (sym-cong₂ (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂) (assoc-sub-ren T₁ τ* (subst←RE ρ)) (assoc-sub-ren T₂ τ* (subst←RE ρ))) ⟩
                        (subst id
                         (sym
                          (cong Value
                           (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                            (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
                         v
                         ≡
                         (ƛ
                          subst id
                          (sym
                           (cong₂ (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂)
                            (assoc-sub-ren T₁ τ* (subst←RE ρ))
                            (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                          e))
                         ∎
            in
            let eq-fun = begin
                          ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
                           (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
                           𝓥⟦ T₁ ⟧ (Tren-act τ* ρ) w z₁ →
                           ∃-syntax
                           (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tren-act τ* ρ) v₁ (z z₁)))
                         ≡⟨ dep-ext (λ w → {!!}) ⟩
                           ((w : Value (Tsub (subst←RE (Tren-act τ* ρ)) T₁))
                            (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                            𝓥⟦ Tren τ* T₁ ⟧ ρ
                            (subst id (cong Value (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))) w)
                            z₁ →
                            Σ (Value (Tsub (subst←RE ρ) (Tren τ* T₂)))
                            (λ v₂ →
                               (subst id
                                (sym
                                 (cong₂ (λ A₁ → Expr [] (A₁ ◁ ∅)) (assoc-sub-ren T₁ τ* (subst←RE ρ))
                                  (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                                e
                                [
                                exp
                                (subst id (cong Value (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))) w)
                                ]E)
                               ⇓ v₂
                               ∧
                               𝓥⟦ Tren τ* T₂ ⟧ ρ v₂
                               (subst id
                                (sym
                                 (cong₂ (λ A₁ A₂ → A₁ → A₂)
                                  (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                                  (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
                                z z₁)))
                         ≡˘⟨ pi-subst (λ w → (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                           𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                           Σ (Value (Tsub (subst←RE ρ) (Tren τ* T₂)))
                           (λ v₂ →
                              (subst id
                               (sym
                                (cong₂ (λ A₁ → Expr [] (A₁ ◁ ∅)) (assoc-sub-ren T₁ τ* (subst←RE ρ))
                                 (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                               e
                               [ exp w ]E)
                              ⇓ v₂
                              ∧
                              𝓥⟦ Tren τ* T₂ ⟧ ρ v₂
                              (subst id
                               (sym
                                (cong₂ (λ A₁ A₂ → A₁ → A₂)
                                 (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                                 (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
                               z z₁))) (cong Value (sym (assoc-sub-ren T₁ τ* (subst←RE ρ)))) ⟩
                          ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                           (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                           𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                           Σ (Value (Tsub (subst←RE ρ) (Tren τ* T₂)))
                           (λ v₂ →
                              (subst id
                               (sym
                                (cong₂ (λ A₁ → Expr [] (A₁ ◁ ∅)) (assoc-sub-ren T₁ τ* (subst←RE ρ))
                                 (assoc-sub-ren T₂ τ* (subst←RE ρ))))
                               e
                               [ exp w ]E)
                              ⇓ v₂
                              ∧
                              𝓥⟦ Tren τ* T₂ ⟧ ρ v₂
                              (subst id
                               (sym
                                (cong₂ (λ A₁ A₂ → A₁ → A₂)
                                 (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                                 (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
                               z z₁)))
                         ∎
            in
            cong₂ _∧_ eq≡ eq-fun)) ⟩
    Σ (Expr [] (Tsub (subst←RE (Tren-act τ* ρ)) T₁ ◁ ∅)
       (Tsub (subst←RE (Tren-act τ* ρ)) T₂))
      (λ e →
         (subst id
          (sym
           (cong Value
            (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
             (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
          v
          ≡
          (ƛ
           subst id
           (sym
            (cong₂ (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂)
             (assoc-sub-ren T₁ τ* (subst←RE ρ))
             (assoc-sub-ren T₂ τ* (subst←RE ρ))))
           e))
         ∧
         ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
          (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
          𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
          Σ (Value (Tsub (subst←RE ρ) (Tren τ* T₂)))
          (λ v₂ →
             (subst id
              (sym
               (cong₂ (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂)
                (assoc-sub-ren T₁ τ* (subst←RE ρ))
                (assoc-sub-ren T₂ τ* (subst←RE ρ))))
              e
              [ exp w ]E)
             ⇓ v₂
             ∧
             𝓥⟦ Tren τ* T₂ ⟧ ρ v₂
             (subst id
              (sym
               (cong₂ (λ A₁ A₂ → A₁ → A₂)
                (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
              z z₁))))
  ≡˘⟨ sigma-subst _ (cong₂ (λ A₁ A₂ → Expr [] (A₁ ◁ ∅) A₂) (assoc-sub-ren T₁ τ* (subst←RE ρ)) (assoc-sub-ren T₂ τ* (subst←RE ρ))) ⟩
    Σ (Expr [] ((Tsub (subst←RE ρ) (Tren τ* T₁)) ◁ ∅) (Tsub (subst←RE ρ) (Tren τ* T₂)))
      (λ e →
         (subst id
          (sym
           (cong Value
            (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
             (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
          v
          ≡ (ƛ e))
         ∧
         ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
          (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
          𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
          Σ _
          (λ v₂ →
             (e [ exp w ]E) ⇓ v₂ ∧
             𝓥⟦ Tren τ* T₂ ⟧ ρ v₂
             (subst id
              (sym
               (cong₂ (λ A₁ A₂ → A₁ → A₂)
                (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
                (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
              z z₁))))
  ≡⟨ cong (λ H → H z) (app-subst (λ f →
         ∃-syntax
         (λ e →
            (subst id
             (sym
              (cong Value
               (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
             v
             ≡ (ƛ e))
            ∧
            ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
             (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
             𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
             ∃-syntax
             (λ v₂ → (e [ exp w ]E) ⇓ v₂ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₂ (f z₁))))) (cong₂ (λ A₁ A₂ → A₁ → A₂)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))) ⟩
    subst (λ Z → Z → Set _)
      (cong₂ (λ A₁ A₂ → A₁ → A₂)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
       (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
      (λ f →
         ∃-syntax
         (λ e →
            (subst id
             (sym
              (cong Value
               (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
                (assoc-sub-ren T₂ τ* (subst←RE ρ)))))
             v
             ≡ (ƛ e))
            ∧
            ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
             (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
             𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
             ∃-syntax
             (λ v₂ → (e [ exp w ]E) ⇓ v₂ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₂ (f z₁)))))
      z
  ≡⟨ cong (λ H → H v z)
     (app-subst (λ v₁ →
         subst (λ Z → Z → Set _)
         (cong₂ (λ A₁ A₂ → A₁ → A₂)
          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
         (λ f →
            ∃-syntax
            (λ e →
               (v₁ ≡ (ƛ e)) ∧
               ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                ∃-syntax
                (λ v₂ → (e [ exp w ]E) ⇓ v₂ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₂ (f z₁)))))) (cong Value
       (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
        (assoc-sub-ren T₂ τ* (subst←RE ρ))))) ⟩
    subst
      (λ v₁ →
         v₁ →
         (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
          ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
         Set _)
      (cong Value
       (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
        (assoc-sub-ren T₂ τ* (subst←RE ρ))))
      (λ v₁ →
         subst (λ Z → Z → Set _)
         (cong₂ (λ A₁ A₂ → A₁ → A₂)
          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
         (λ f →
            ∃-syntax
            (λ e →
               (v₁ ≡ (ƛ e)) ∧
               ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                ∃-syntax
                (λ v₂ → (e [ exp w ]E) ⇓ v₂ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₂ (f z₁))))))
      v z
  ≡˘⟨ cong (λ H → H v z) (subst-∘ {P = (λ v₁ → v₁ →
         (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
          ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
         Set _)} {f = Value} 
      (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
       (assoc-sub-ren T₂ τ* (subst←RE ρ)))) ⟩
    subst
      (λ v₁ →
         Value v₁ →
         (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
          ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
         Set _)
      (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
       (assoc-sub-ren T₂ τ* (subst←RE ρ)))
      (λ v₁ →
         subst (λ Z → Z → Set _)
         (cong₂ (λ A₁ A₂ → A₁ → A₂)
          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
          (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
         (λ f →
            ∃-syntax
            (λ e →
               (v₁ ≡ (ƛ e)) ∧
               ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                ∃-syntax
                (λ v₂ → (e [ exp w ]E) ⇓ v₂ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₂ (f z₁))))))
      v z

  ≡˘⟨ cong
        (λ H →
           subst
           (λ v₁ →
              Value v₁ →
              (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
               ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
              Set _)
           (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
            (assoc-sub-ren T₂ τ* (subst←RE ρ)))
           H v z)
        (eta-subst (λ u f →
                ∃-syntax
                (λ e →
                   (u ≡ (ƛ e)) ∧
                   ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                    (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                    𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                    ∃-syntax
                    (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₁ (f z₁))))) (cong₂ (λ A₁ A₂ → A₁ → A₂)
              (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
              (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))) ⟩
          subst
            (λ v₁ →
               Value v₁ →
               (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) []) →
                ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tren-act τ* ρ)) [])) →
               Set _)
            (cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ))
             (assoc-sub-ren T₂ τ* (subst←RE ρ)))
            (subst
             (λ zz →
                Value
                (Tsub (subst←RE ρ) (Tren τ* T₁) ⇒ Tsub (subst←RE ρ) (Tren τ* T₂)) →
                zz → Set _)
             (cong₂ (λ A₁ A₂ → A₁ → A₂)
              (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
              (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
             (λ u f →
                ∃-syntax
                (λ e →
                   (u ≡ (ƛ e)) ∧
                   ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                    (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                    𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                    ∃-syntax
                    (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₁ (f z₁))))))
      v z

  ≡˘⟨ cong (λ H → H v z) 
           (subst₂-subst-subst (λ vv zz → Value vv → zz → Set _) 
             ((cong₂ _⇒_ (assoc-sub-ren T₁ τ* (subst←RE ρ)) (assoc-sub-ren T₂ τ* (subst←RE ρ))))
             ((cong₂ (λ A₁ A₂ → A₁ → A₂)
               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
               (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂)))
             (λ u f →
               (∃[ e ]
                  (u ≡ (ƛ e)) ∧
                  ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
                   (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
                   𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
                   ∃-syntax
                   (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₁ (f z₁)))))) ⟩
    subst₂ (λ vv zz → Value vv → zz → Set _)
      (cong₂ _⇒_ 
        (assoc-sub-ren T₁ τ* (subst←RE ρ))
        (assoc-sub-ren T₂ τ* (subst←RE ρ)))
      (cong₂ (λ A₁ A₂ → A₁ → A₂)
        (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₁)
        (Tren*-preserves-semantics (τ*∈Ren* τ* (subst←RE ρ)) T₂))
      (λ u f →
         (∃[ e ]
            (u ≡ (ƛ e)) ∧
            ((w : Value (Tsub (subst←RE ρ) (Tren τ* T₁)))
             (z₁ : ⟦ Tren τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
             𝓥⟦ Tren τ* T₁ ⟧ ρ w z₁ →
             ∃-syntax
             (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ Tren τ* T₂ ⟧ ρ v₁ (f z₁)))))
      v z
  ∎ 
LRVren-eq′ (`∀α l , T) ρ τ* v z = {!!}
LRVren-eq′ `ℕ ρ τ* v z = refl
