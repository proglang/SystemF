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
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst; subst-subst-sym; subst-sym-subst; -- Properties
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
  ≡⟨ sym (fusion-Tsub-Tsub T (Textₛ Tidₛ T′) (subst←RE ρ)) ⟩
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

Tsub-act-REext-ext : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → ∀ l₂ x₂ → (REext (Tsub-act τ* ρ) (T′ , R)) l₂ x₂ ≡ Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)) l₂ x₂
Tsub-act-REext-ext ρ τ* T′ R l₂ here = refl
Tsub-act-REext-ext {l = l} ρ τ* T′ R l₂ (there x) =
  let ρ* = subst←RE ρ in
  let T₂ = τ* l₂ x in
  let F = λ ⟦x⟧ → (Expr [] ∅ (Tsub ρ* T₂) → ⟦x⟧ → Set l₂) in
  let eq₂ = subst-preserves ρ* T₂ in
  let ρ*r = subst←RE (REext ρ (T′ , R)) in
  let T₂r = (Tliftₛ τ* l) l₂ (there x) in
  let Fr = λ ⟦x⟧ → (Expr [] ∅ (Tsub ρ*r T₂r) → ⟦x⟧ → Set l₂) in
  let eq₂r = subst-preserves ρ*r T₂r in
  let eq-1 = begin
               Tsub (subst←RE ρ) (τ* l₂ x)
             ≡˘⟨ fusion-Tsub-Tren (τ* l₂ x) (Twkᵣ Tidᵣ) (Textₛ (subst←RE ρ) T′)  ⟩
               Tsub (Textₛ (subst←RE ρ) T′) (Twk (τ* l₂ x))
             ≡˘⟨ cong (λ σ → Tsub σ (Twk (τ* l₂ x))) (subst←RE-ext-ext ρ T′ R) ⟩
               Tsub (subst←RE (REext ρ (T′ , R))) (Twk (τ* l₂ x))
             ∎ in
  let eq-2 = begin
          subst REL eq-1 (subst F (sym eq₂) (𝓥⟦ τ* l₂ x ⟧ ρ))
        ≡⟨ {!!} ⟩
          {!!}
        ≡⟨ cong (subst Fr (sym eq₂r)) {!LRVren!} ⟩
          subst Fr (sym eq₂r) (𝓥⟦ Twk (τ* l₂ x) ⟧ (REext ρ (T′ , R)))
        ∎ in
  begin
    Tsub-act τ* ρ l₂ x
  ≡⟨ refl ⟩
    Tsub ρ* T₂ , subst F (sym eq₂) (𝓥⟦ T₂ ⟧ ρ)
  ≡⟨ dcong₂ _,_ eq-1 eq-2 ⟩
    Tsub ρ*r T₂r , subst Fr (sym eq₂r) (𝓥⟦ T₂r ⟧ (REext ρ (T′ , R)))
  ≡⟨ refl ⟩
    Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)) l₂ (there x)
  ∎

Tsub-act-REext : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → (REext (Tsub-act τ* ρ) (T′ , R)) ≡ω Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R))
Tsub-act-REext ρ τ* T′ R = relenv-ext (Tsub-act-REext-ext ρ τ* T′ R)


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
       (subst Value (sym (fusion-Tsub-Tsub T τ* (subst←RE ρ))) v)
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
  → 𝓥⟦ Tsub τ* T ⟧ ρ (subst Value (sym (fusion-Tsub-Tsub T τ* (subst←RE ρ))) v)
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
  let eq-T₁ = (fusion-Tsub-Tsub T₁ τ* (subst←RE ρ)) in
  let eq-T₂ = (fusion-Tsub-Tsub T₂ τ* (subst←RE ρ)) in
  subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (sym eq-T₁) (sym eq-T₂) e ,
  subst-split-ƛ (sym (fusion-Tsub-Tsub (T₁ ⇒ T₂) τ* (subst←RE ρ))) (sym eq-T₁) (sym eq-T₂) e ,
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
        let eq-1 = (sym
                      (trans
                       (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                        (subst-preserves τ* T₂))
                       (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η)
                        (subst-to-env*-comp τ* (subst←RE ρ) [])))) in
        let eq-2 = (sym
                      (begin
                       step-≡
                       (⟦ Tsub τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) []) →
                        ⟦ Tsub τ* T₂ ⟧ (subst-to-env* (subst←RE ρ) []))
                       (step-≡
                        (⟦ T₁ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) →
                         ⟦ T₂ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
                        (_ ≡⟨⟩
                         (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                          ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                         ∎)
                        (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η)
                         (subst-to-env*-comp τ* (subst←RE ρ) [])))
                       (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                        (subst-preserves τ* T₂)))) in
        subst (𝓥⟦ Tsub τ* T₂ ⟧ ρ (subst Value (sym eq-T₂) v₂))
              (begin
                subst id (sym eq-z2) (z (subst id eq-z z₁))
              ≡⟨ dist-subst z eq-z (sym (trans (subst-preserves τ* (T₁ ⇒ T₂)) (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η) (subst-to-env*-comp τ* (subst←RE ρ) [])))) (sym eq-z2) z₁ ⟩
                cong (λ f → f z₁) (subst-irrelevant {F = id} eq-1 eq-2 z)
              )
              lrv-t2-v′

LRVsubst (`∀α l , T) ρ τ* v z (e , v≡Λe , F) =
  let eqᵢ = begin
             Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T
            ≡⟨ refl ⟩
             Tsub (Tliftₛ (τ* ∘ₛₛ subst←RE ρ) l) T
            ≡˘⟨ assoc-sub↑-sub↑ T τ*  (subst←RE ρ) ⟩
              Tsub (Tliftₛ (subst←RE ρ) l) (Tsub (Tliftₛ τ* l) T)
            ∎ in
  let eqₒ = sym (cong (`∀α_,_ l) (assoc-sub↑-sub↑ T τ* (subst←RE ρ))) in
  let sub₁ = subst Value eqₒ in
  subst (Expr (l ∷ []) (l ◁* ∅)) eqᵢ e ,
  (begin
    sub₁ v
  ≡⟨ cong sub₁ v≡Λe ⟩
    sub₁ (Λ l ⇒ e)
  ≡⟨ subst-split-Λ eqₒ eqᵢ e ⟩
    Λ l ⇒ subst (Expr (l ∷ []) (l ◁* ∅)) eqᵢ e
  ∎) , 
  λ T′ R → F T′ R |> λ where
    (vT[T′] , e[T′]⇓vT[T′] , lrv-t-ρ′) →
      let eqᵥ = (cong (Tsub (Textₛ Tidₛ T′)) (sym (assoc-sub↑-sub↑ T τ* (subst←RE ρ)))) in
      let subᵥ = subst Value eqᵥ in
      subᵥ vT[T′] ,
      let r = subst-split-⇓₂ eqᵥ e[T′]⇓vT[T′] in
      subst id
            (cong (_⇓ subᵥ vT[T′])
              (sym (dist-subst' {F = Expr _ _} {G = Value} (_[ T′ ]T) (λ e′ → e′ [ T′ ]ET) eqᵢ eqᵥ e )))
            r
      ,
      let eq-vtt = (begin
                     (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T)
                   ≡⟨ σ↑T[T′]≡TextₛσT′T (subst←RE (Tsub-act τ* ρ)) T′ T ⟩
                     Tsub (Textₛ (subst←RE (Tsub-act τ* ρ)) T′) T
                   ≡˘⟨ cong (λ σ → Tsub σ T) (subst←RE-ext-ext (Tsub-act τ* ρ) T′ R) ⟩
                     Tsub (subst←RE (REext (Tsub-act τ* ρ) (T′ , R))) T
                   ≡⟨ congωl (λ ρ → Tsub (subst←RE ρ) T) (Tsub-act-REext ρ τ* T′ R) ⟩
                     Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T
                   ∎) in
      let lrv = LRVsubst T
                         (REext ρ (T′ , R))
                         (Tliftₛ τ* l)
                         (subst Value eq-vtt vT[T′])
                         (substω ⟦ T ⟧ (congωω (⟦ T′ ⟧ [] ∷_)
                                         (conglω (λ σ → subst-to-env* σ [])
                                           (trans
                                             (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                             (congωl (λ ρ → Tdropₛ (subst←RE ρ)) (Tsub-act-REext ρ τ* T′ R)))))
                                       (z (⟦ T′ ⟧ [])))
                         (dep-substωll (𝓥⟦ T ⟧)
                                       (Tsub-act-REext ρ τ* T′ R)
                                       (trans
                                         (substω-∘ Value (λ ρ → Tsub (subst←RE ρ) T) (Tsub-act-REext ρ τ* T′ R))
                                         (trans
                                           (subst-subst {P = Value} (lemma1 (Tsub-act τ* ρ) T T′ R) {y≡z = (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R))})
                                           (subst-irrelevant (trans (lemma1 (Tsub-act τ* ρ) T T′ R)
                                                                    (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R)))
                                                             (begin
                                                               step-≡ (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T)
                                                               (step-≡˘ (Tsub (Textₛ (subst←RE (Tsub-act τ* ρ)) T′) T)
                                                               (step-≡ (Tsub (subst←RE (REext (Tsub-act τ* ρ) (T′ , R))) T)
                                                               (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                                               (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R)))
                                                               (cong (λ σ → Tsub σ T) (subst←RE-ext-ext (Tsub-act τ* ρ) T′ R)))
                                                               (σ↑T[T′]≡TextₛσT′T (subst←RE (Tsub-act τ* ρ)) T′ T))
                                                             vT[T′])))
                                       (trans
                                         (substω-∘ (λ{ (σ₀ , σ) → ⟦ T ⟧ (⟦ σ₀ ⟧ [] ∷ subst-to-env* σ [])}) (λ ρ → let σ = subst←RE ρ in (σ l here , Tdropₛ σ)) (Tsub-act-REext ρ τ* T′ R))
                                         (trans
                                           (subst-∘ {P = id}{f = (λ { (σ₀ , σ) → ⟦ T ⟧ (⟦ σ₀ ⟧ [] ∷ subst-to-env* σ []) })}
                                                    (congωl (λ ρ₁ → subst←RE ρ₁ l here , Tdropₛ (subst←RE ρ₁)) (Tsub-act-REext ρ τ* T′ R)))
                                           (trans
                                             (subst-irrelevant (cong (λ { (σ₀ , σ) → ⟦ T ⟧ (⟦ σ₀ ⟧ [] ∷ subst-to-env* σ []) })
                                                               (congωl (λ ρ₁ → subst←RE ρ₁ l here , Tdropₛ (subst←RE ρ₁))
                                                               (Tsub-act-REext ρ τ* T′ R)))
                                                               (congωl ⟦ T ⟧
                                                                 (congωω (⟦ T′ ⟧ [] ∷_)
                                                                   (conglω (λ σ → subst-to-env* σ [])
                                                                     (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                                                       (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁)) (Tsub-act-REext ρ τ* T′ R))))))
                                                               (z (⟦ T′ ⟧ [])))
                                             (sym (substω-∘ id ⟦ T ⟧ (congωω (⟦ T′ ⟧ [] ∷_)
                                                                     (conglω (λ σ → subst-to-env* σ [])
                                                                       (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
                                                                              (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
                                                                                      (Tsub-act-REext ρ τ* T′ R))))))))))
                                       lrv-t-ρ′) in
      subst₂ (𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R)))
             (trans (subst-subst {P = Value} (begin
                                                step-≡ (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T)
                                                (step-≡˘ (Tsub (Textₛ (subst←RE (Tsub-act τ* ρ)) T′) T)
                                                 (step-≡ (Tsub (subst←RE (REext (Tsub-act τ* ρ) (T′ , R))) T)
                                                  (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
                                                  (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R)))
                                                 (cong (λ σ → Tsub σ T) (subst←RE-ext-ext (Tsub-act τ* ρ) T′ R)))
                                                (σ↑T[T′]≡TextₛσT′T (subst←RE (Tsub-act τ* ρ)) T′ T))
                                              {y≡z = (sym (fusion-Tsub-Tsub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))})
                     (trans
                       (subst-irrelevant {F = Value} _ _ vT[T′])
                       (sym (subst-subst {P = Value} (cong (Tsub (Textₛ Tidₛ T′)) (sym (assoc-sub↑-sub↑ T τ* (subst←RE ρ))))
                                                     {y≡z = (lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R)}))))
             {!!}
             lrv 

LRVsubst `ℕ ρ τ* v z (n , v≡#n , n≡z) =
  n ,
  v≡#n ,
  trans n≡z (sym (subst-id id _))

LRVsubst′ T ρ τ* v z x = {!!}
