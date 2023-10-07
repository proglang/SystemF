{-# OPTIONS --allow-unsolved-metas #-}
module LRVsubst where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; -- Properties
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


Text-sub-sub : ∀ {l′}{Δ₁}{Δ₂}
  → (σ* : TSub Δ₁ Δ₂)
  → (T′ : Type Δ₁ l′)
  → (x : Level)
  → (y : x ∈ (l′ ∷ Δ₁))
  → Textₛ σ* (Tsub σ* T′) x y ≡
      (Textₛ Tidₛ T′ ∘ₛₛ σ*) x y
Text-sub-sub σ* T′ x here = refl
Text-sub-sub σ* T′ x (there y) = refl

ext-σ-T′≡σ[T′] :
  (T′        : Type Δ l′)
  (T         : Type (l′ ∷ Δ) l)
  (ρ         : RelEnv Δ)
  (R′        : REL (Tsub (subst←RE ρ) T′))
  → Tsub (subst←RE (REext ρ (Tsub (subst←RE ρ) T′ , R′))) T ≡ Tsub (subst←RE ρ) (T [ T′ ]T)
ext-σ-T′≡σ[T′] T′ T ρ R′ =
  begin
    Tsub (subst←RE (REext ρ (Tsub (subst←RE ρ) T′ , R′))) T
  ≡⟨ cong (λ τ → Tsub τ T) (subst←RE-ext-ext ρ (Tsub (subst←RE ρ) T′) R′) ⟩
    Tsub (Textₛ (subst←RE ρ) (Tsub (subst←RE ρ) T′)) T
  ≡⟨ cong (λ τ → Tsub τ T) (fun-ext₂ (Text-sub-sub (subst←RE ρ) T′)) ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛₛ subst←RE ρ) T
  ≡⟨ sym (assoc-sub-sub T (Textₛ Tidₛ T′) (subst←RE ρ)) ⟩
    Tsub (subst←RE ρ) (T [ T′ ]T)
  ∎ 

dist-substω :
  ∀ {ℓ ℓ' ℓ₁} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : B → Setω}
  → (a→b : A → B)
  → (f : ∀ {a} → F a → G (a→b a))
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ω substωl G b₁≡b₂ (f {a₁} x)
dist-substω _ _ refl refl _ = refl

dist-subst-special : ∀ {la}{lv}{lr}
  → {R : Set lr} {A A′ A″ : Set la} {V : Set lv}
  → (f : V → A′ → R)
  → (eq₁ : A′ ≡ A″)
  → (eq₂ : A ≡ A″)
  → (eq₃ : A ≡ A′)
  → (v : V)
  → (z : A)
  → subst (λ A → (V → A → R)) eq₁ f v (subst id eq₂ z)  ≡ f v (subst id eq₃ z)
dist-subst-special f refl refl refl v z = refl

-- generalizing to general type substitution

Tsub-act : TSub Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tsub-act σ* ρ = λ l x →
  let ρ* = subst←RE ρ in
  let T₂ = σ* l x in
  Tsub ρ* T₂ , subst (λ ⟦x⟧ → (Expr [] ∅ (Tsub ρ* T₂) → ⟦x⟧ → Set l)) (sym (subst-preserves (subst←RE ρ) T₂)) (𝓥⟦ T₂ ⟧ ρ)

-- holds definitionally
subst←RE-sub : ∀ (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂)
  → (l′ : Level) (x : l′ ∈ Δ₁) → subst←RE (Tsub-act τ* ρ) l′ x ≡ (τ* ∘ₛₛ subst←RE ρ) l′ x
subst←RE-sub ρ τ* l′ x = refl

LRVsubst : ∀ {Δ₁}{Δ₂}{l}
  → (T : Type Δ₁ l)
  → (ρ : RelEnv Δ₂)
  → (τ* : TSub Δ₁ Δ₂)
  → let ρ* = subst←RE ρ
  in (v : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T))
  → (z : ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
  → 𝓥⟦ T ⟧ (Tsub-act τ* ρ) v z
  → 𝓥⟦ Tsub τ* T ⟧ ρ 
       (subst Value (sym (assoc-sub-sub T τ* (subst←RE ρ))) v)
       (subst id (sym (begin
                        ⟦ Tsub τ* T ⟧ (subst-to-env* (subst←RE ρ) [])
                      ≡⟨ subst-preserves τ* T ⟩
                        ⟦ T ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
                      ≡⟨ congωl ⟦ T ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
                        ⟦ T ⟧ (subst-to-env* (τ* ∘ₛₛ subst←RE ρ) [])
                      ≡⟨⟩
                        ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
                      ∎)) z)

LRVsubst′ :  ∀ {Δ₁}{Δ₂}{l}
  → (T : Type Δ₁ l)
  → (ρ : RelEnv Δ₂)
  → (τ* : TSub Δ₁ Δ₂)
  → let ρ* = subst←RE ρ
  in (v : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T))
  → (z : ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
  → 𝓥⟦ Tsub τ* T ⟧ ρ (subst Value (sym (assoc-sub-sub T τ* (subst←RE ρ))) v)
                     (subst id (sym (begin
                        ⟦ Tsub τ* T ⟧ (subst-to-env* (subst←RE ρ) [])
                      ≡⟨ subst-preserves τ* T ⟩
                        ⟦ T ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
                      ≡⟨ congωl ⟦ T ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
                        ⟦ T ⟧ (subst-to-env* (τ* ∘ₛₛ subst←RE ρ) [])
                      ≡⟨⟩
                        ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
                      ∎)) z)
  → 𝓥⟦ T ⟧ (Tsub-act τ* ρ) v z

LRVsubst′ T ρ τ* v z x = {!!}

LRVsubst {l = l} (` x) ρ τ* v z lrv-t =
  let F₁ = (λ ⟦x⟧ → Expr [] ∅ (Tsub (subst←RE ρ) (τ* l x)) → ⟦x⟧ → Set l) in
  let eq₁ = (sym (subst-preserves (subst←RE ρ) (τ* l x))) in
  let sub₁ = subst F₁ eq₁ in
  let eq₂ = (sym
        (subst-var-preserves x
         (subst←RE
          (λ l₁ x₁ →
             Tsub (subst←RE ρ) (τ* l₁ x₁) ,
             subst
             (λ ⟦x⟧ → Expr [] ∅ (Tsub (subst←RE ρ) (τ* l₁ x₁)) → ⟦x⟧ → Set l₁)
             (sym (subst-preserves (subst←RE ρ) (τ* l₁ x₁))) (𝓥⟦ τ* l₁ x₁ ⟧ ρ)))
         [])) in
  let eq₃ = (sym
        (begin
         step-≡ (⟦ τ* l x ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (apply-env (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) x)
          (_ ≡⟨⟩ apply-env (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) x ∎)
          (congωl (λ η → apply-env η x)
           (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-var-preserves x τ* (subst-to-env* (subst←RE ρ) [])))) in
  subst id (begin 
             sub₁ (𝓥⟦ τ* l x ⟧ ρ) v (subst id eq₂ z)
           ≡⟨ dist-subst-special (𝓥⟦ τ* l x ⟧ ρ) eq₁ eq₂ eq₃ v z ⟩
             𝓥⟦ τ* l x ⟧ ρ v (subst id eq₃ z)
           ∎) lrv-t

LRVsubst (T₁ ⇒ T₂) ρ τ* v z (e , refl , F) =
  let eq-T₁ = (assoc-sub-sub T₁ τ* (subst←RE ρ)) in
  let eq-T₂ = (assoc-sub-sub T₂ τ* (subst←RE ρ)) in
  subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (sym eq-T₁) (sym eq-T₂) e ,
  subst-split-ƛ (sym (assoc-sub-sub (T₁ ⇒ T₂) τ* (subst←RE ρ))) (sym eq-T₁) (sym eq-T₂) e ,
  λ w₁ z₁ lrv-sub-t1 →
  let σ* = subst←RE ρ in
  let w₁′ = (subst Value eq-T₁ w₁) in
  let eq-z = (begin
                       ⟦ Tsub τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])
                     ≡⟨ subst-preserves τ* T₁ ⟩
                       ⟦ T₁ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
                     ≡⟨ congωl ⟦ T₁ ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
                       ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
                     ∎) in
  let eq-z2 = (begin
                       ⟦ Tsub τ* T₂ ⟧ (subst-to-env* (subst←RE ρ) [])
                     ≡⟨ subst-preserves τ* T₂ ⟩
                       ⟦ T₂ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
                     ≡⟨ congωl ⟦ T₂ ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
                       ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
                     ∎) in
  let z₁′ = subst id eq-z z₁ in
  let lrv-sub-t1′ = LRVsubst′ T₁ ρ τ* w₁′ z₁′ (subst₂ (𝓥⟦ Tsub τ* T₁ ⟧ ρ) (sym (subst-sym-subst {P = Value} eq-T₁)) (sym (subst-sym-subst {P = id} eq-z)) lrv-sub-t1) in
    F w₁′ z₁′ lrv-sub-t1′ |> λ where
      (v₂ , e[w₁]⇓v₂ , lrv-t2-v) →
        subst Value (sym eq-T₂) v₂ ,
        let eq-⇓ = begin (subst₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄) (sym eq-T₁) (sym eq-T₂) e [ exp w₁ ]E)
                       ⇓ subst Value (sym eq-T₂) v₂
                  ≡˘⟨ cong (_⇓ subst Value (sym eq-T₂) v₂)
                           (subst-split-[]E e (exp w₁) (sym eq-T₁) (sym eq-T₂) ) ⟩
                     subst Value (sym eq-T₂) (e [ subst Value (sym (sym eq-T₁)) (exp w₁) ]E)
                           ⇓ subst Value (sym eq-T₂) v₂
                  ≡˘⟨ cong
                       (λ e′ →
                          subst Value (sym eq-T₂) (e [ e′ ]E) ⇓
                          subst Value (sym eq-T₂) v₂)
                       (dist-subst' {F = Value} {G = Value} id exp eq-T₁ (sym (sym eq-T₁)) w₁) ⟩
                     subst Value (sym eq-T₂) (e [ exp (subst Value eq-T₁ w₁) ]E) ⇓ subst Value (sym eq-T₂) v₂
                  ∎ in
        let e[w₁]⇓v₂′ = subst-split-⇓₂ (sym eq-T₂) e[w₁]⇓v₂ in
        subst id (sym eq-⇓) e[w₁]⇓v₂′ , 
        let lrv-t2-v′ = LRVsubst T₂ ρ τ* v₂ (z z₁′) lrv-t2-v in
        subst (𝓥⟦ Tsub τ* T₂ ⟧ ρ (subst Value (sym eq-T₂) v₂))
              (begin subst id (sym eq-z2) (z (subst id eq-z z₁))
              ≡⟨ dist-subst z eq-z (sym (trans (subst-preserves τ* (T₁ ⇒ T₂)) (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η) (subst-to-env*-comp τ* (subst←RE ρ) [])))) (sym eq-z2) z₁ ⟩
              cong (λ f → f z₁) (subst-irrelevant {F = id} _ _ z) 
              )
              lrv-t2-v′
LRVsubst (`∀α l , T) ρ τ* v z lrv-t = {!!}
LRVsubst `ℕ ρ τ* v z (n , v≡#n , n≡z) = 
  n ,
  v≡#n ,
  trans n≡z (sym (subst-id id _))

-- the case for single substitution (not sufficiently general)

LRVsubst1 : ∀ {Δ}{l}{l′}
  → (Γ : TEnv Δ)
  → (ρ : RelEnv Δ)
  → let η = (subst-to-env* (subst←RE ρ) [])
  in (T′ : Type Δ l′)
  → let T′-closed = Tsub (subst←RE ρ) T′
  in (R′ : REL T′-closed)
  → let ρ′ = (REext ρ (T′-closed , R′))
  in (T : Type (l′ ∷ Δ) l)
  → (v : Value (Tsub (subst←RE ρ′) T))
  → (z : ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η))
  → 𝓥⟦ T ⟧ ρ′ v (subst (λ ⟦T′⟧ → ⟦ T ⟧ (⟦T′⟧ ∷ η)) (sym (subst-preserves (subst←RE ρ) T′)) z)
  → 𝓥⟦ T [ T′ ]T ⟧ ρ
        (subst Value (ext-σ-T′≡σ[T′] T′ T ρ R′) v)
        (subst id (sym (Tsingle-subst-preserves η T′ T)) z)
LRVsubst1 Γ ρ T′ R′ (` x) v z lrv-t = {! !}
LRVsubst1 Γ ρ T′ R′ (T₁ ⇒ T₂) v z lrv-t = {!!}
LRVsubst1 Γ ρ T′ R′ (`∀α l , T) v z lrv-t = {! !}
LRVsubst1 Γ ρ T′ R′ `ℕ v z (n , v≡#n , n≡z) =
  n ,
  trans (subst-id Value (ext-σ-T′≡σ[T′] T′ `ℕ ρ R′)) v≡#n ,
  trans n≡z (trans (subst-∘ {P = id} {f = λ ⟦T′⟧ → ℕ} (sym (subst-preserves (subst←RE ρ) T′)))
                   (subst-irrelevant (cong (λ ⟦T′⟧ → ℕ) (sym (subst-preserves (subst←RE ρ) T′)))
                                     (sym (Tsingle-subst-preserves (subst-to-env* (subst←RE ρ) []) T′ `ℕ)) z))
