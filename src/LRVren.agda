module LRVren where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; -- Properties
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


eta-subst₂ : ∀ {lv lz lr}
  → {V₁ V₂ : Set lv} {Z₁ Z₂ : Set lz} {R : Set lr}
  → (h : V₁ → Z₁ → R)
  → (v₁≡v₂ : V₁ ≡ V₂)
  → (z₁≡z₂ : Z₁ ≡ Z₂)
  → subst₂ (λ V Z → V → Z → R) v₁≡v₂ z₁≡z₂ h ≡ λ v₂ z₂ → h (subst id (sym v₁≡v₂) v₂) (subst id (sym z₁≡z₂) z₂)
eta-subst₂ h refl refl = refl

subst₂-subst-subst : ∀ {lv lz lr}
  → {V : Set lv} {Z : Set lz} {R : Set lr}
  → {v₁ v₂ : V}{z₁ z₂ : Z}
  → (F : V → Z → Set lr)
  → (v₁≡v₂ : v₁ ≡ v₂)
  → (z₁≡z₂ : z₁ ≡ z₂)
  → (x : F v₁ z₁)
  → subst₂ F v₁≡v₂ z₁≡z₂ x ≡ subst (λ v → F v z₂) v₁≡v₂ (subst (F v₁) z₁≡z₂ x)
subst₂-subst-subst F refl refl x = refl

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
  ≡⟨ {!!} ⟩
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
