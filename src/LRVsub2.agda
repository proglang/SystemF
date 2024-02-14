{-# OPTIONS --allow-unsolved-metas #-}
module LRVsub2 where

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
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        sym-cong; subst-∘; subst-application; subst-application′; subst-subst; subst-subst-sym; subst-sym-subst; -- Properties
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
open import Logical2
open import LRVren2

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

--
Tren-act-wk-ext : ∀ (ρ : RelEnv Δ) (T′ : Type [] l) (R : REL T′)
  → (Tren-act (Twkᵣ Tidᵣ) (REext ρ (T′ , R))) ≡ω ρ
Tren-act-wk-ext ρ T′ R =
  relenv-ext (helper ρ T′ R)
  where
  helper :  ∀ (ρ : RelEnv Δ) (T′ : Type [] l) (R : REL T′) l₁ (x : l₁ ∈ Δ)
    → Tren-act (Twkᵣ Tidᵣ) (REext ρ (T′ , R)) l₁ x ≡ ρ l₁ x
  helper ρ T′ R l₁ here = refl
  helper ρ T′ R l₁ (there x) = refl

-- generalizing to general type substitution

Tsub-act : TSub Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tsub-act σ* ρ = λ l x →
  let ρ* = subst←RE ρ in
  let T₂ = σ* l x in
  Tsub ρ* T₂ , subst (λ ⟦x⟧ → (Value (Tsub ρ* T₂) → ⟦x⟧ → Set l)) (sym (subst-preserves (subst←RE ρ) T₂)) (𝓥⟦ T₂ ⟧ ρ)

--
subst-Tsub-act : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) → subst←RE (Tsub-act τ* ρ) ≡ (τ* ∘ₛₛ subst←RE ρ)
subst-Tsub-act ρ τ* = fun-ext₂ (helper ρ τ*)
  where
  helper : ∀ (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (l : Level) (x : l ∈ Δ₁)
    → subst←RE (Tsub-act τ* ρ) l x ≡ (τ* ∘ₛₛ subst←RE ρ) l x
  helper ρ τ* l here = refl
  helper ρ τ* l (there x) = refl

--
Tsub-act-REext-ext : (ρ : RelEnv Δ₂) (τ* : TSub Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → ∀ l₂ x₂ → (REext (Tsub-act τ* ρ) (T′ , R)) l₂ x₂ ≡ Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)) l₂ x₂
Tsub-act-REext-ext ρ τ* T′ R l₂ here = refl
Tsub-act-REext-ext {l = l} ρ τ* T′ R l₂ (there x) =
  let ρ* = subst←RE ρ in
  let Tₓ = τ* l₂ x in
  let F = λ ⟦x⟧ → (Value (Tsub ρ* Tₓ) → ⟦x⟧ → Set l₂) in
  let eq₂ = subst-preserves ρ* Tₓ in
  let ρ*r = subst←RE (REext ρ (T′ , R)) in
  let Tₓr = (Tliftₛ τ* l) l₂ (there x) in
  let Fr = λ ⟦x⟧ → (Value (Tsub ρ*r Tₓr) → ⟦x⟧ → Set l₂) in
  let eq₂r = subst-preserves ρ*r Tₓr in
  let eq-1 = begin
               Tsub (subst←RE ρ) (τ* l₂ x)
             ≡˘⟨ assoc-sub-ren (τ* l₂ x) (Twkᵣ Tidᵣ) (Textₛ (subst←RE ρ) T′)  ⟩
               Tsub (Textₛ (subst←RE ρ) T′) (Twk (τ* l₂ x))
             ≡˘⟨ cong (λ σ → Tsub σ (Twk (τ* l₂ x))) (subst←RE-ext-ext ρ T′ R) ⟩
               Tsub (subst←RE (REext ρ (T′ , R))) (Twk (τ* l₂ x))
             ∎ in
  let eq-ren = LRVren-eq Tₓ (REext ρ (T′ , R)) (Twkᵣ Tidᵣ) in
  let eq-2 = begin
          subst REL eq-1
            (subst F (sym eq₂)
              (𝓥⟦ Tₓ ⟧ ρ))
        ≡⟨ subst*-irrelevant (⟨ F , sym eq₂ ⟩∷ ⟨ REL , eq-1 ⟩∷ [] )
                             (⟨ (λ zz → Value (Tsub (Twkᵣ Tidᵣ ∘ᵣₛ ρ*r) Tₓ) → zz → Set l₂) , (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ)) ⟩∷
                              ⟨ (λ v → Value v → ⟦ Tren (Twkᵣ Tidᵣ) Tₓ ⟧ (subst-to-env* ρ*r []) → Set l₂) , (sym (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r)) ⟩∷
                              ⟨ Fr , sym eq₂r ⟩∷
                              [])
                             (𝓥⟦ Tₓ ⟧ ρ) ⟩
          subst Fr (sym eq₂r)
            (subst (λ v → Value v → ⟦ Tren (Twkᵣ Tidᵣ) Tₓ ⟧ (subst-to-env* ρ*r []) → Set l₂) (sym (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (subst (λ zz → Value (Tsub (Twkᵣ Tidᵣ ∘ᵣₛ ρ*r) Tₓ) → zz → Set l₂) (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
              (𝓥⟦ Tₓ ⟧ ρ)))
        ≡˘⟨ cong (subst Fr (sym eq₂r))
           (subst₂-subst-subst (λ vv zz → Value vv → zz → Set l₂)
                               (sym (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r))
                               (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
                               (𝓥⟦ Tₓ ⟧ ρ)) ⟩
          subst Fr (sym eq₂r)
            (subst₂ (λ vv zz → Value vv → zz → Set l₂)
             (sym (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
             (𝓥⟦ Tₓ ⟧ ρ))
        ≡⟨ cong (subst Fr (sym eq₂r))
           (cong (subst₂ (λ vv zz → Value vv → zz → Set l₂)
             (sym (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ)))
             (dcongωl (𝓥⟦ Tₓ ⟧) refl)) ⟩
          subst Fr (sym eq₂r)
            (subst₂ (λ vv zz → Value vv → zz → Set l₂)
             (sym (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r))
             (sym (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ))
             (𝓥⟦ Tₓ ⟧ (Tren-act (Twkᵣ Tidᵣ) (REext ρ (T′ , R)))))
        ≡⟨ cong (subst Fr (sym eq₂r))
                (subst₂-swap′ (assoc-sub-ren Tₓ (Twkᵣ Tidᵣ) ρ*r)
                              (Tren*-preserves-semantics (τ*∈Ren* (Twkᵣ Tidᵣ) ρ*r) Tₓ)
                              _
                              _
                              eq-ren) ⟩
          subst Fr (sym eq₂r) (𝓥⟦ Twk (τ* l₂ x) ⟧ (REext ρ (T′ , R)))
        ∎ in
  begin
    Tsub-act τ* ρ l₂ x
  ≡⟨ refl ⟩
    Tsub ρ* Tₓ , subst F (sym eq₂) (𝓥⟦ Tₓ ⟧ ρ)
  ≡⟨ dcong₂ _,_ eq-1 eq-2 ⟩
    Tsub ρ*r Tₓr , subst Fr (sym eq₂r) (𝓥⟦ Tₓr ⟧ (REext ρ (T′ , R)))
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

LRVsub : ∀ {Δ₁}{Δ₂}{l}
  → (T : Type Δ₁ l)
  → (ρ : RelEnv Δ₂)
  → (τ* : TSub Δ₁ Δ₂)
  → let ρ* = subst←RE ρ
  in (v : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T))
  → (z : ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
  → 𝓥⟦ T ⟧ (Tsub-act τ* ρ) v z
  ≡ 𝓥⟦ Tsub τ* T ⟧ ρ
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

LRVsub (` α) ρ τ* v z =
  let T₂ = τ* _ α in
  let ρ* = subst←RE ρ in
  begin
    𝓥⟦ ` α ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    proj₂ (Tsub-act τ* ρ _ α) v (subst id (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) z)
  ≡⟨ refl ⟩
    subst (λ ⟦x⟧ → Value (Tsub ρ* T₂) → ⟦x⟧ → Set _)
      (sym (subst-preserves (subst←RE ρ) T₂))
      (𝓥⟦ T₂ ⟧ ρ)
      v
      (subst id (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) z)
  ≡⟨ cong (λ ∎ → ∎ v (subst id (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) z))
    (eta-subst (λ v z → 𝓥⟦ T₂ ⟧ ρ v z) (sym (subst-preserves (subst←RE ρ) T₂)) ) ⟩
    subst (λ Z → Z → Set _) (sym (subst-preserves ρ* T₂))
      (λ z₁ → 𝓥⟦ T₂ ⟧ ρ v z₁)
      (subst id
       (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) z)
  ≡⟨ cong (λ ∎ → ∎ (subst id (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) z))
    (sym (app-subst (λ z₁ → 𝓥⟦ T₂ ⟧ ρ v z₁) (sym (subst-preserves ρ* T₂)))) ⟩
    𝓥⟦ T₂ ⟧ ρ v
      (subst id (sym (sym (subst-preserves ρ* T₂)))
       (subst id
        (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) z))
  ≡⟨ cong (𝓥⟦ T₂ ⟧ ρ v)
    (subst-subst {P = id} (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []))
                           {(sym (sym (subst-preserves ρ* T₂)))}
                           {z}) ⟩
    𝓥⟦ T₂ ⟧ ρ v
      (subst id
       (trans (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) []))
        (sym (sym (subst-preserves ρ* T₂))))
       z)
  ≡⟨ cong (𝓥⟦ T₂ ⟧ ρ v)
    (subst-irrelevant {F = id}
                      (trans (sym (subst-var-preserves α (subst←RE (Tsub-act τ* ρ)) [])) (sym (sym (subst-preserves ρ* T₂))))
                      (sym
        (step-≡ (⟦ T₂ ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (apply-env (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) α)
          (apply-env (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) α ∎)
          (congωl (λ η → apply-env η α)
           (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-var-preserves α τ* (subst-to-env* (subst←RE ρ) []))))
         z) ⟩
    𝓥⟦ T₂ ⟧ ρ v
      (subst id
       (sym
        (step-≡ (⟦ T₂ ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (apply-env (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) α)
          (apply-env (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) α ∎)
          (congωl (λ η → apply-env η α)
           (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-var-preserves α τ* (subst-to-env* (subst←RE ρ) []))))
       z)
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* (` α) ⟧ ρ
      (subst Value (sym (assoc-sub-sub (` α) τ* (subst←RE ρ))) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* (` α) ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡
          (⟦ ` α ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
          (⟦ ` α ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ ` α ⟧ (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-preserves τ* (` α))))
       z)
  ∎
LRVsub (T₁ ⇒ T₂) ρ τ* v z =
  let η = subst-to-env* (subst←RE ρ) [] in
  let ρ* = subst←RE ρ in
  let eq-T : ∀ {l} (T : Type _ l) → Tsub (subst←RE (Tsub-act τ* ρ)) T ≡ Tsub ρ* (Tsub τ* T)
      eq-T T =
        begin
          Tsub (subst←RE (Tsub-act τ* ρ)) T
        ≡⟨ refl ⟩
          Tsub (τ* ∘ₛₛ ρ*) T
        ≡˘⟨ assoc-sub-sub T τ* (subst←RE ρ) ⟩
          Tsub ρ* (Tsub τ* T)
        ∎

      fₗ = (λ e →
         (exp v ≡ (ƛ e)) ∧
         ((w : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ → (e [ exp w ]E) ⇓ v₁ ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁))))
  in
  begin
    𝓥⟦ T₁ ⇒ T₂ ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    Σ (Expr [] (Tsub (subst←RE (Tsub-act τ* ρ)) T₁ ◁ ∅) (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
      fₗ
  ≡⟨ sigma-subst fₗ (cong₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (eq-T T₁) (eq-T T₂)) ⟩
    Σ (Expr [] (Tsub ρ* (Tsub τ* T₁) ◁ ∅) (Tsub ρ* (Tsub τ* T₂)))
      (λ e →
         (exp v ≡
          (ƛ
           subst id
           (sym
            (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
               (assoc-sub-sub T₁ τ* ρ*))
              refl)
             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
               (assoc-sub-sub T₂ τ* ρ*))
              refl)))
           e))
         ∧
         ((w : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
          𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
          ∃-syntax
          (λ v₁ →
             (subst id
              (sym
               (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                  (assoc-sub-sub T₁ τ* ρ*))
                 refl)
                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                  (assoc-sub-sub T₂ τ* ρ*))
                 refl)))
              e
              [ exp w ]E)
             ⇓ v₁
             ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁))))
  ≡⟨ cong (Σ (Expr [] (Tsub ρ* (Tsub τ* T₁) ◁ ∅) (Tsub ρ* (Tsub τ* T₂))))
      (fun-ext (λ e →
        cong₂ _∧_
      --------------------------------------------------
        (begin
          exp v ≡
            (ƛ
             subst id
             (sym
              (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (assoc-sub-sub T₁ τ* ρ*))
                refl)
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (assoc-sub-sub T₂ τ* ρ*))
                refl)))
             e)
        ≡⟨ cong (exp v ≡_)
          (cong (λ ∎ → (ƛ subst id ∎ e))
            (sym-cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (assoc-sub-sub T₁ τ* ρ*))
                refl)
                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (assoc-sub-sub T₂ τ* ρ*))
                refl))) ⟩
          exp v ≡
            (ƛ
             subst id
             (cong₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (assoc-sub-sub T₁ τ* ρ*))
                refl))
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (assoc-sub-sub T₂ τ* ρ*))
                refl)))
             e)
        ≡˘⟨ cong (exp v ≡_)
           (cong ƛ_
             (subst₂-∘ id (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄)
             (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (assoc-sub-sub T₁ τ* ρ*))
                refl))
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                 (assoc-sub-sub T₂ τ* ρ*))
                refl)) e)) ⟩
          exp v ≡
            (ƛ
             subst₂ (id Function.∘₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄))
             (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (assoc-sub-sub T₁ τ* ρ*))
               refl))
             (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (assoc-sub-sub T₂ τ* ρ*))
               refl))
             e)
        ≡˘⟨ cong (exp v ≡_)
            (subst-split-ƛ (cong₂ _⇒_ (sym (eq-T T₁)) (sym (eq-T T₂)))
            (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (assoc-sub-sub T₁ τ* ρ*))
               refl))
             (sym
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (assoc-sub-sub T₂ τ* ρ*))
               refl)) e ) ⟩
          exp v ≡ (subst CExpr (cong₂ _⇒_ (sym (eq-T T₁)) (sym (eq-T T₂))) (ƛ e))
        ≡˘⟨ cong (exp v ≡_)
          (cong (λ ∎ → subst CExpr ∎ (ƛ e))
          (sym-cong₂ _⇒_
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (assoc-sub-sub T₁ τ* ρ*))
               refl)
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (assoc-sub-sub T₂ τ* ρ*))
               refl))) ⟩
          exp v ≡
            subst CExpr
            (sym
             (cong₂ _⇒_
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                (assoc-sub-sub T₁ τ* ρ*))
               refl)
              (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
               (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                (assoc-sub-sub T₂ τ* ρ*))
               refl)))
            (ƛ e)
        ≡˘⟨ subst-swap-eq {F = CExpr} (cong₂ _⇒_ (eq-T T₁) (eq-T T₂)) (exp v) (ƛ e) ⟩
          subst CExpr (cong₂ _⇒_ (eq-T T₁) (eq-T T₂)) (exp v) ≡ (ƛ e)
        ≡˘⟨ cong (_≡ (ƛ e))
            (dist-subst' {F = Value} {G = CExpr} id exp
                          (sym (cong₂ _⇒_ (assoc-sub-sub T₁ τ* ρ*) (assoc-sub-sub T₂ τ* ρ*)))
                          (cong₂ _⇒_ (eq-T T₁) (eq-T T₂))
                          v) ⟩
          exp (subst Value (sym (cong₂ _⇒_ (assoc-sub-sub T₁ τ* ρ*) (assoc-sub-sub T₂ τ* ρ*))) v)
            ≡ (ƛ e)
        ∎)
      --------------------------------------------------
        (begin
          ((w : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₁))
            (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
            𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
            ∃-syntax
            (λ v₁ →
               (subst id
                (sym
                 (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                    (assoc-sub-sub T₁ τ* ρ*))
                   refl)
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                    (assoc-sub-sub T₂ τ* ρ*))
                   refl)))
                e
                [ exp w ]E)
               ⇓ v₁
               ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
        ≡⟨ pi-subst
             (λ w →
                (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
                𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ) w z₁ →
                ∃-syntax
                (λ v₁ →
                   (subst id
                    (sym
                     (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                      (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                       (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                        (assoc-sub-sub T₁ τ* ρ*))
                       refl)
                      (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                       (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                        (assoc-sub-sub T₂ τ* ρ*))
                       refl)))
                    e
                    [ exp w ]E)
                   ⇓ v₁
                   ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
             (cong Value (sym (eq-T T₁))) ⟩
          ((w : Value (Tsub ρ* (Tsub τ* T₁))) →
          (z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
            𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
            (subst id
             (cong Value
              (sym
               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                 (assoc-sub-sub T₁ τ* ρ*))
                refl)))
             w)
            z₁ →
            ∃-syntax
            (λ v₁ →
               (subst id
                (sym
                 (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                    (assoc-sub-sub T₁ τ* ρ*))
                   refl)
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                    (assoc-sub-sub T₂ τ* ρ*))
                   refl)))
                e
                [
                exp
                (subst id
                 (cong Value
                  (sym
                   (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                    (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                     (assoc-sub-sub T₁ τ* ρ*))
                    refl)))
                 w)
                ]E)
               ⇓ v₁
               ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
        ≡⟨ dep-ext (λ w → 
           begin
             ((z₁ : ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])) →
               𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
               (subst id
                (cong Value
                 (sym
                  (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                   (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                    (assoc-sub-sub T₁ τ* ρ*))
                   refl)))
                w)
               z₁ →
               ∃-syntax
               (λ v₁ →
                  (subst id
                   (sym
                    (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                     (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                      (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                       (assoc-sub-sub T₁ τ* ρ*))
                      refl)
                     (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                      (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                       (assoc-sub-sub T₂ τ* ρ*))
                      refl)))
                   e
                   [
                   exp
                   (subst id
                    (cong Value
                     (sym
                      (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                       (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                        (assoc-sub-sub T₁ τ* ρ*))
                       refl)))
                    w)
                   ]E)
                  ⇓ v₁
                  ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
           ≡⟨ pi-subst
                (λ z₁ →
                   𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                   (subst id
                    (cong Value
                     (sym
                      (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                       (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                        (assoc-sub-sub T₁ τ* ρ*))
                       refl)))
                    w)
                   z₁ →
                   ∃-syntax
                   (λ v₁ →
                      (subst id
                       (sym
                        (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                           (assoc-sub-sub T₁ τ* ρ*))
                          refl)
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                           (assoc-sub-sub T₂ τ* ρ*))
                          refl)))
                       e
                       [
                       exp
                       (subst id
                        (cong Value
                         (sym
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (assoc-sub-sub T₁ τ* ρ*))
                           refl)))
                        w)
                       ]E)
                      ⇓ v₁
                      ∧ 𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁ (z z₁)))
                (trans (subst-preserves {η₂ = η} τ* T₁)
                       (sym (congωl (⟦ T₁ ⟧)
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                                    (symω (subst-to-env*-comp τ* ρ* [])))))) ⟩
             ((z₁ : ⟦ Tsub τ* T₁ ⟧ η) → 𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                                          (subst id
                                           (cong Value
                                            (sym
                                             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                               (assoc-sub-sub T₁ τ* ρ*))
                                              refl)))
                                           w)
                                          (subst id (trans (subst-preserves τ* T₁) _) z₁) →
                                          ∃-syntax
                                          (λ v₁ →
                                             (subst id
                                              (sym
                                               (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                                                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                                  (assoc-sub-sub T₁ τ* ρ*))
                                                 refl)
                                                (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                                                 (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                                                  (assoc-sub-sub T₂ τ* ρ*))
                                                 refl)))
                                              e
                                              [
                                              exp
                                              (subst id
                                               (cong Value
                                                (sym
                                                 (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                                  (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                                   (assoc-sub-sub T₁ τ* ρ*))
                                                  refl)))
                                               w)
                                              ]E)
                                             ⇓ v₁
                                             ∧
                                             𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                                             (z (subst id (trans (subst-preserves τ* T₁) _) z₁))))
           ≡⟨ dep-ext (λ z₁ →
              begin
                (𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                  (subst id
                   (cong Value
                    (sym
                     (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                      (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                       (assoc-sub-sub T₁ τ* ρ*))
                      refl)))
                   w)
                  (subst id
                   (trans (subst-preserves τ* T₁)
                    (sym
                     (congωl ⟦ T₁ ⟧
                      (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                       (symω (subst-to-env*-comp τ* ρ* []))))))
                   z₁) →
                  ∃-syntax
                  (λ v₁ →
                     (subst id
                      (sym
                       (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                        (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                         (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                          (assoc-sub-sub T₁ τ* ρ*))
                         refl)
                        (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                         (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                          (assoc-sub-sub T₂ τ* ρ*))
                         refl)))
                      e
                      [
                      exp
                      (subst id
                       (cong Value
                        (sym
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                           (assoc-sub-sub T₁ τ* ρ*))
                          refl)))
                       w)
                      ]E)
                     ⇓ v₁
                     ∧
                     𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                     (z
                      (subst id
                       (trans (subst-preserves τ* T₁)
                        (sym
                         (congωl ⟦ T₁ ⟧
                          (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                           (symω (subst-to-env*-comp τ* ρ* []))))))
                       z₁))))
              ≡⟨ cong₂ (λ X Y → X → Y)
        --------------------------------------------------
                (begin
                  𝓥⟦ T₁ ⟧ (Tsub-act τ* ρ)
                    (subst id
                     (cong Value
                      (sym
                       (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                        (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                         (assoc-sub-sub T₁ τ* ρ*))
                        refl)))
                     w)
                    (subst id
                     (trans (subst-preserves τ* T₁)
                      (sym
                       (congωl ⟦ T₁ ⟧
                        (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                         (symω (subst-to-env*-comp τ* ρ* []))))))
                     z₁)
                ≡⟨ LRVsub T₁ ρ τ*
                            (subst id
                     (cong Value
                      (sym
                       (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                        (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                         (assoc-sub-sub T₁ τ* ρ*))
                        refl)))
                     w)
                     (subst id
                     (trans (subst-preserves τ* T₁)
                      (sym
                       (congωl ⟦ T₁ ⟧
                        (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                         (symω (subst-to-env*-comp τ* ρ* []))))))
                     z₁) ⟩
                  𝓥⟦ Tsub τ* T₁ ⟧ ρ
                    (subst Value (sym (assoc-sub-sub T₁ τ* ρ*))
                     (subst id
                      (cong Value
                       (sym
                        (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                         (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                          (assoc-sub-sub T₁ τ* ρ*))
                         refl)))
                      w))
                    (subst id
                     (sym
                      (step-≡ (⟦ Tsub τ* T₁ ⟧ η)
                       (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η))
                        (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                        (congωl ⟦ T₁ ⟧ (subst-to-env*-comp τ* ρ* [])))
                       (subst-preserves τ* T₁)))
                     (subst id
                      (trans (subst-preserves τ* T₁)
                       (sym
                        (congωl ⟦ T₁ ⟧
                         (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                          (symω (subst-to-env*-comp τ* ρ* []))))))
                      z₁))
                ≡⟨ cong₂ (𝓥⟦ Tsub τ* T₁ ⟧ ρ)
                   (subst*-irrelevant
                     (⟨ id , (cong Value (sym
                                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                              (assoc-sub-sub T₁ τ* ρ*))
                                             refl))) ⟩∷
                     ⟨ Value , (sym (assoc-sub-sub T₁ τ* ρ*)) ⟩∷
                     []) [] w)
                   (subst*-irrelevant
                     (⟨ id , (trans (subst-preserves τ* T₁)
                                    (sym
                                     (congωl ⟦ T₁ ⟧
                                      (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                                       (symω (subst-to-env*-comp τ* ρ* [])))))) ⟩∷
                      ⟨ id , (sym
                               (step-≡ (⟦ Tsub τ* T₁ ⟧ η)
                                (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η))
                                 (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                                 (congωl ⟦ T₁ ⟧ (subst-to-env*-comp τ* ρ* [])))
                                (subst-preserves τ* T₁))) ⟩∷
                      [])
                     []
                     z₁) ⟩
                  𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁
                ∎)
        --------------------------------------------------
                (begin
                  Σ (Value (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                    (λ v₁ →
                       (subst id
                        (sym
                         (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (assoc-sub-sub T₁ τ* ρ*))
                           refl)
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (assoc-sub-sub T₂ τ* ρ*))
                           refl)))
                        e
                        [
                        exp
                        (subst id
                         (cong Value
                          (sym
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (assoc-sub-sub T₁ τ* ρ*))
                            refl)))
                         w)
                        ]E)
                       ⇓ v₁
                       ∧
                       𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                       (z
                        (subst id
                         (trans (subst-preserves τ* T₁)
                          (sym
                           (congωl ⟦ T₁ ⟧
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                             (symω (subst-to-env*-comp τ* ρ* []))))))
                         z₁)))
                ≡⟨ sigma-subst (λ v₁ →
                       (subst id
                        (sym
                         (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (assoc-sub-sub T₁ τ* ρ*))
                           refl)
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (assoc-sub-sub T₂ τ* ρ*))
                           refl)))
                        e
                        [
                        exp
                        (subst id
                         (cong Value
                          (sym
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (assoc-sub-sub T₁ τ* ρ*))
                            refl)))
                         w)
                        ]E)
                       ⇓ v₁
                       ∧
                       𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ) v₁
                       (z
                        (subst id
                         (trans (subst-preserves τ* T₁)
                          (sym
                           (congωl ⟦ T₁ ⟧
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                             (symω (subst-to-env*-comp τ* ρ* []))))))
                         z₁)))
                         (cong Value (eq-T T₂)) ⟩
                  Σ (Value (Tsub ρ* (Tsub τ* T₂)))
                    (λ v₁ →
                       (subst id
                        (sym
                         (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                            (assoc-sub-sub T₁ τ* ρ*))
                           refl)
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (assoc-sub-sub T₂ τ* ρ*))
                           refl)))
                        e
                        [
                        exp
                        (subst id
                         (cong Value
                          (sym
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (assoc-sub-sub T₁ τ* ρ*))
                            refl)))
                         w)
                        ]E)
                       ⇓
                       subst id
                       (sym
                        (cong Value
                         (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                          (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                           (assoc-sub-sub T₂ τ* ρ*))
                          refl)))
                       v₁
                       ∧
                       𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ)
                       (subst id
                        (sym
                         (cong Value
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (assoc-sub-sub T₂ τ* ρ*))
                           refl)))
                        v₁)
                       (z
                        (subst id
                         (trans (subst-preserves τ* T₁)
                          (sym
                           (congωl ⟦ T₁ ⟧
                            (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                             (symω (subst-to-env*-comp τ* ρ* []))))))
                         z₁)))
                ≡⟨ cong (Σ (Value (Tsub ρ* (Tsub τ* T₂))))
                  (fun-ext (λ v₁ →
                    cong₂ _∧_
                --------------------------------------------------
                    (begin
                      (subst id
                         (sym
                          (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                             (assoc-sub-sub T₁ τ* ρ*))
                            refl)
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                             (assoc-sub-sub T₂ τ* ρ*))
                            refl)))
                         e
                         [
                         exp
                         (subst id
                          (cong Value
                           (sym
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                              (assoc-sub-sub T₁ τ* ρ*))
                             refl)))
                          w)
                         ]E)
                        ⇓
                        subst id
                        (sym
                         (cong Value
                          (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                           (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                            (assoc-sub-sub T₂ τ* ρ*))
                           refl)))
                        v₁
                    ≡⟨ cong (_ ⇓_)
                       (cong (λ ∎ → subst id ∎ v₁)
                         (sym-cong {f = Value} (trans (sym (assoc-sub-sub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎)))) ⟩
                      subst (Expr [] ∅) (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst (Expr [] ∅)
                           (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp
                            (subst id
                             (cong Value
                              (sym
                               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                 (assoc-sub-sub T₁ τ* ρ*))
                                refl)))
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                              (assoc-sub-sub T₁ τ* ρ*))
                             refl)
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                              (assoc-sub-sub T₂ τ* ρ*))
                             refl)))
                          e))
                        ⇓
                        subst id
                        (cong Value
                         (sym
                          (trans (sym (assoc-sub-sub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎))))
                        v₁
                    ≡˘⟨ cong (_ ⇓_) (subst-∘ {P = id} {f = Value}
                                              (sym (trans (sym (assoc-sub-sub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎))) {v₁}) ⟩
                      subst (Expr [] ∅) (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₂))
                        (Esub Tidₛ
                         (Eextₛ Tidₛ Eidₛ
                          (subst (Expr [] ∅)
                           (sym (TidₛT≡T (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)))
                           (exp
                            (subst id
                             (cong Value
                              (sym
                               (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                                (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                                 (assoc-sub-sub T₁ τ* ρ*))
                                refl)))
                             w))))
                         (subst id
                          (sym
                           (cong₂ (λ T₃ → Expr [] (T₃ ◁ ∅))
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₁)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₁) (Tsub ρ* (Tsub τ* T₁) ∎)
                              (assoc-sub-sub T₁ τ* ρ*))
                             refl)
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                              (assoc-sub-sub T₂ τ* ρ*))
                             refl)))
                          e))
                        ⇓
                        subst Value
                        (sym (trans (sym (assoc-sub-sub T₂ τ* ρ*)) (Tsub ρ* (Tsub τ* T₂) ∎)))
                        v₁
                    ≡⟨ {!!} ⟩
                      {!!}
                    ≡⟨ {!!} ⟩
                      (e [ exp w ]E) ⇓ v₁
                    ∎)
                --------------------------------------------------
                    (begin
                      𝓥⟦ T₂ ⟧ (Tsub-act τ* ρ)
                        (subst id
                         (sym
                          (cong Value
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                             (assoc-sub-sub T₂ τ* ρ*))
                            refl)))
                         v₁)
                        (z
                         (subst id
                          (trans (subst-preserves τ* T₁)
                           (sym
                            (congωl ⟦ T₁ ⟧
                             (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                              (symω (subst-to-env*-comp τ* ρ* []))))))
                          z₁))
                    ≡⟨ LRVsub T₂ ρ τ*
                                (subst id
                         (sym
                          (cong Value
                           (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                            (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                             (assoc-sub-sub T₂ τ* ρ*))
                            refl)))
                         v₁)
                        (z
                         (subst id
                          (trans (subst-preserves τ* T₁)
                           (sym
                            (congωl ⟦ T₁ ⟧
                             (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                              (symω (subst-to-env*-comp τ* ρ* []))))))
                          z₁)) ⟩
                      𝓥⟦ Tsub τ* T₂ ⟧ ρ
                        (subst Value (sym (assoc-sub-sub T₂ τ* ρ*))
                         (subst id
                          (sym
                           (cong Value
                            (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                             (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                              (assoc-sub-sub T₂ τ* ρ*))
                             refl)))
                          v₁))
                        (subst id
                         (sym
                          (step-≡ (⟦ Tsub τ* T₂ ⟧ η)
                           (step-≡ (⟦ T₂ ⟧ (subst-to-env* τ* η))
                            (⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
                            (congωl ⟦ T₂ ⟧ (subst-to-env*-comp τ* ρ* [])))
                           (subst-preserves τ* T₂)))
                         (z
                          (subst id
                           (trans (subst-preserves τ* T₁)
                            (sym
                             (congωl ⟦ T₁ ⟧
                              (transω (conglω (λ σ → subst-to-env* σ []) (subst-Tsub-act ρ τ*))
                               (symω (subst-to-env*-comp τ* ρ* []))))))
                           z₁)))
                    ≡⟨ cong₂ (𝓥⟦ Tsub τ* T₂ ⟧ ρ)
                --------------------------------------------------
                      (subst*-irrelevant
                        (⟨ id , (sym
                            (cong Value
                             (step-≡ (Tsub (subst←RE (Tsub-act τ* ρ)) T₂)
                              (step-≡˘ (Tsub (τ* ∘ₛₛ ρ*) T₂) (Tsub ρ* (Tsub τ* T₂) ∎)
                               (assoc-sub-sub T₂ τ* ρ*))
                              refl))) ⟩∷
                         ⟨ Value , (sym (assoc-sub-sub T₂ τ* ρ*)) ⟩∷
                         [])
                        []
                        v₁)
                --------------------------------------------------
                      {!!}
                --------------------------------------------------
                     ⟩
                      𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                        (subst id
                         (sym
                          (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                           (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                            ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                              ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                             ∎)
                            (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                             (subst-to-env*-comp τ* ρ* [])))
                           (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                            (subst-preserves τ* T₂))))
                         z z₁)
                    ∎)
                --------------------------------------------------
                    )) ⟩
                  Σ (Value (Tsub ρ* (Tsub τ* T₂)))
                    (λ v₁ →
                       (e [ exp w ]E) ⇓ v₁ ∧
                       𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                       (subst id
                        (sym
                         (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                          (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                           ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                             ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                            ∎)
                           (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                            (subst-to-env*-comp τ* ρ* [])))
                          (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                           (subst-preserves τ* T₂))))
                        z z₁))
                ∎)
        --------------------------------------------------
                ⟩
                (𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
                  ∃-syntax
                  (λ v₁ →
                     (e [ exp w ]E) ⇓ v₁ ∧
                     𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                     (subst id
                      (sym
                       (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                        (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                         ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                           ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                          ∎)
                         (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                          (subst-to-env*-comp τ* ρ* [])))
                        (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                         (subst-preserves τ* T₂))))
                      z z₁)))
              ∎) ⟩
             ((z₁ : ⟦ Tsub τ* T₁ ⟧ η) →
               𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
               ∃-syntax
               (λ v₁ →
                  (e [ exp w ]E) ⇓ v₁ ∧
                  𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
                  (subst id
                   (sym
                    (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                     (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                      ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                        ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                       ∎)
                      (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                       (subst-to-env*-comp τ* ρ* [])))
                     (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                      (subst-preserves τ* T₂))))
                   z z₁)))
           ∎) ⟩
          ((w : Value (Tsub ρ* (Tsub τ* T₁))) (z₁ : ⟦ Tsub τ* T₁ ⟧ η) →
            𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
            ∃-syntax
            (λ v₁ →
               (e [ exp w ]E) ⇓ v₁ ∧
               𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
               (subst id
                (sym
                 (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                  (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                   ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                     ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                    ∎)
                   (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                    (subst-to-env*-comp τ* ρ* [])))
                  (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                   (subst-preserves τ* T₂))))
                z z₁)))
        ∎)
      --------------------------------------------------
        )) ⟩
    Σ (Expr [] (Tsub ρ* (Tsub τ* T₁) ◁ ∅) (Tsub ρ* (Tsub τ* T₂)))
      (λ e →
         (exp (subst Value (sym (cong₂ _⇒_ (assoc-sub-sub T₁ τ* ρ*) (assoc-sub-sub T₂ τ* ρ*))) v) ≡ (ƛ e))
         ∧
         ((w : Value (Tsub ρ* (Tsub τ* T₁))) (z₁ : ⟦ Tsub τ* T₁ ⟧ η) →
          𝓥⟦ Tsub τ* T₁ ⟧ ρ w z₁ →
          ∃-syntax
          (λ v₁ →
             (e [ exp w ]E) ⇓ v₁ ∧
             𝓥⟦ Tsub τ* T₂ ⟧ ρ v₁
             (subst id
              (sym
               (step-≡ (⟦ Tsub τ* T₁ ⟧ η → ⟦ Tsub τ* T₂ ⟧ η)
                (step-≡ (⟦ T₁ ⟧ (subst-to-env* τ* η) → ⟦ T₂ ⟧ (subst-to-env* τ* η))
                 ((⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
                   ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
                  ∎)
                 (congωl (λ η₁ → ⟦ T₁ ⟧ η₁ → ⟦ T₂ ⟧ η₁)
                  (subst-to-env*-comp τ* ρ* [])))
                (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
                 (subst-preserves τ* T₂))))
              z z₁))))
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* (T₁ ⇒ T₂) ⟧ ρ
      (subst Value (sym (assoc-sub-sub (T₁ ⇒ T₂) τ* ρ*)) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* (T₁ ⇒ T₂) ⟧ η)
         (step-≡
          (⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* τ* η))
          (⟦ T₁ ⇒ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ T₁ ⇒ T₂ ⟧ (subst-to-env*-comp τ* ρ* [])))
         (subst-preserves τ* (T₁ ⇒ T₂))))
       z)
  ∎
LRVsub (`∀α l , T) ρ τ* v z = {!!}
LRVsub `ℕ ρ τ* v z =
  begin
    𝓥⟦ `ℕ ⟧ (Tsub-act τ* ρ) v z
  ≡⟨ refl ⟩
    Σ ℕ (λ n → (proj₁ v ≡ # n) × (n ≡ z))
  ≡⟨ cong (Σ ℕ)
     (fun-ext (λ n → cong (Σ (proj₁ v ≡ (# n)))
       (fun-ext (λ x → cong (n ≡_)
         (subst-irrelevant {F = id} refl (sym (trans (congωl (λ η → ℕ) (subst-to-env*-comp τ* (λ l x₁ → proj₁ (ρ l x₁)) [])) refl)) z))))) ⟩
    Σ ℕ (λ n →
         (proj₁ v ≡ (# n)) × (n ≡ subst id (sym (trans (congωl (λ η → ℕ) (subst-to-env*-comp τ* (λ l x₁ → proj₁ (ρ l x₁)) [])) refl)) z))
  ≡⟨ refl ⟩
    𝓥⟦ Tsub τ* `ℕ ⟧ ρ
      (subst Value (sym (assoc-sub-sub `ℕ τ* (subst←RE ρ))) v)
      (subst id
       (sym
        (step-≡ (⟦ Tsub τ* `ℕ ⟧ (subst-to-env* (subst←RE ρ) []))
         (step-≡ (⟦ `ℕ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
          (⟦ `ℕ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) ∎)
          (congωl ⟦ `ℕ ⟧ (subst-to-env*-comp τ* (subst←RE ρ) [])))
         (subst-preserves{η₂ = subst-to-env* (subst←RE ρ) []} τ* `ℕ)))
       z)
  ∎

-- LRVsubst′ :  ∀ {Δ₁}{Δ₂}{l}
--   → (T : Type Δ₁ l)
--   → (ρ : RelEnv Δ₂)
--   → (τ* : TSub Δ₁ Δ₂)
--   → let ρ* = subst←RE ρ
--   in (v : Value (Tsub (subst←RE (Tsub-act τ* ρ)) T))
--   → (z : ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
--   → 𝓥⟦ Tsub τ* T ⟧ ρ (subst Value (sym (assoc-sub-sub T τ* (subst←RE ρ))) v)
--                      (subst id (sym (begin
--                         ⟦ Tsub τ* T ⟧ (subst-to-env* (subst←RE ρ) [])
--                       ≡⟨ subst-preserves τ* T ⟩
--                         ⟦ T ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
--                       ≡⟨ congωl ⟦ T ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
--                         ⟦ T ⟧ (subst-to-env* (τ* ∘ₛₛ subst←RE ρ) [])
--                       ≡⟨⟩
--                         ⟦ T ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
--                       ∎)) z)
--   → 𝓥⟦ T ⟧ (Tsub-act τ* ρ) v z

-- LRVsubst {l = l} (` x) ρ τ* v z lrv-t =
--   let F₁ = (λ ⟦x⟧ → Expr [] ∅ (Tsub (subst←RE ρ) (τ* l x)) → ⟦x⟧ → Set l) in
--   let eq₁ = (sym (subst-preserves (subst←RE ρ) (τ* l x))) in
--   let sub₁ = subst F₁ eq₁ in
--   let eq₂ = (sym
--         (subst-var-preserves x
--          (subst←RE
--           (λ l₁ x₁ →
--              Tsub (subst←RE ρ) (τ* l₁ x₁) ,
--              subst
--              (λ ⟦x⟧ → Expr [] ∅ (Tsub (subst←RE ρ) (τ* l₁ x₁)) → ⟦x⟧ → Set l₁)
--              (sym (subst-preserves (subst←RE ρ) (τ* l₁ x₁))) (𝓥⟦ τ* l₁ x₁ ⟧ ρ)))
--          [])) in
--   let eq₃ = (sym
--         (begin
--          step-≡ (⟦ τ* l x ⟧ (subst-to-env* (subst←RE ρ) []))
--          (step-≡
--           (apply-env (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) x)
--           (_ ≡⟨⟩ apply-env (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) x ∎)
--           (congωl (λ η → apply-env η x)
--            (subst-to-env*-comp τ* (subst←RE ρ) [])))
--          (subst-var-preserves x τ* (subst-to-env* (subst←RE ρ) [])))) in
--   subst id (begin 
--              sub₁ (𝓥⟦ τ* l x ⟧ ρ) v (subst id eq₂ z)
--            ≡⟨ dist-subst-special (𝓥⟦ τ* l x ⟧ ρ) eq₁ eq₂ eq₃ v z ⟩
--              𝓥⟦ τ* l x ⟧ ρ v (subst id eq₃ z)
--            ∎) lrv-t

-- LRVsubst (T₁ ⇒ T₂) ρ τ* v z (e , refl , F) =
--   let eq-T₁ = (assoc-sub-sub T₁ τ* (subst←RE ρ)) in
--   let eq-T₂ = (assoc-sub-sub T₂ τ* (subst←RE ρ)) in
--   subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (sym eq-T₁) (sym eq-T₂) e ,
--   subst-split-ƛ (sym (assoc-sub-sub (T₁ ⇒ T₂) τ* (subst←RE ρ))) (sym eq-T₁) (sym eq-T₂) e ,
--   λ w₁ z₁ lrv-sub-t1 →
--   let σ* = subst←RE ρ in
--   let w₁′ = (subst Value eq-T₁ w₁) in
--   let eq-z = (begin
--                        ⟦ Tsub τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) [])
--                      ≡⟨ subst-preserves τ* T₁ ⟩
--                        ⟦ T₁ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
--                      ≡⟨ congωl ⟦ T₁ ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
--                        ⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
--                      ∎) in
--   let eq-z2 = (begin
--                        ⟦ Tsub τ* T₂ ⟧ (subst-to-env* (subst←RE ρ) [])
--                      ≡⟨ subst-preserves τ* T₂ ⟩
--                        ⟦ T₂ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) []))
--                      ≡⟨ congωl ⟦ T₂ ⟧ (subst-to-env*-comp τ* (subst←RE ρ) []) ⟩
--                        ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) [])
--                      ∎) in
--   let z₁′ = subst id eq-z z₁ in
--   let lrv-sub-t1′ = LRVsubst′ T₁ ρ τ* w₁′ z₁′ (subst₂ (𝓥⟦ Tsub τ* T₁ ⟧ ρ) (sym (subst-sym-subst {P = Value} eq-T₁)) (sym (subst-sym-subst {P = id} eq-z)) lrv-sub-t1) in
--     F w₁′ z₁′ lrv-sub-t1′ |> λ where
--       (v₂ , e[w₁]⇓v₂ , lrv-t2-v) →
--         subst Value (sym eq-T₂) v₂ ,
--         let eq-⇓ = begin (subst₂ (λ T₃ T₄ → Expr [] (T₃ ◁ ∅) T₄) (sym eq-T₁) (sym eq-T₂) e [ exp w₁ ]E)
--                        ⇓ subst Value (sym eq-T₂) v₂
--                   ≡˘⟨ cong (_⇓ subst Value (sym eq-T₂) v₂)
--                            (subst-split-[]E e (exp w₁) (sym eq-T₁) (sym eq-T₂) ) ⟩
--                      subst Value (sym eq-T₂) (e [ subst Value (sym (sym eq-T₁)) (exp w₁) ]E)
--                            ⇓ subst Value (sym eq-T₂) v₂
--                   ≡˘⟨ cong
--                        (λ e′ →
--                           subst Value (sym eq-T₂) (e [ e′ ]E) ⇓
--                           subst Value (sym eq-T₂) v₂)
--                        (dist-subst' {F = Value} {G = Value} id exp eq-T₁ (sym (sym eq-T₁)) w₁) ⟩
--                      subst Value (sym eq-T₂) (e [ exp (subst Value eq-T₁ w₁) ]E) ⇓ subst Value (sym eq-T₂) v₂
--                   ∎ in
--         let e[w₁]⇓v₂′ = subst-split-⇓₂ (sym eq-T₂) e[w₁]⇓v₂ in
--         subst id (sym eq-⇓) e[w₁]⇓v₂′ , 
--         let lrv-t2-v′ = LRVsubst T₂ ρ τ* v₂ (z z₁′) lrv-t2-v in
--         let eq-1 = (sym
--                       (trans
--                        (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
--                         (subst-preserves τ* T₂))
--                        (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η)
--                         (subst-to-env*-comp τ* (subst←RE ρ) [])))) in
--         let eq-2 = (sym
--                       (begin
--                        step-≡
--                        (⟦ Tsub τ* T₁ ⟧ (subst-to-env* (subst←RE ρ) []) →
--                         ⟦ Tsub τ* T₂ ⟧ (subst-to-env* (subst←RE ρ) []))
--                        (step-≡
--                         (⟦ T₁ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])) →
--                          ⟦ T₂ ⟧ (subst-to-env* τ* (subst-to-env* (subst←RE ρ) [])))
--                         (_ ≡⟨⟩
--                          (⟦ T₁ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []) →
--                           ⟦ T₂ ⟧ (subst-to-env* (subst←RE (Tsub-act τ* ρ)) []))
--                          ∎)
--                         (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η)
--                          (subst-to-env*-comp τ* (subst←RE ρ) [])))
--                        (cong₂ (λ A B → A → B) (subst-preserves τ* T₁)
--                         (subst-preserves τ* T₂)))) in
--         subst (𝓥⟦ Tsub τ* T₂ ⟧ ρ (subst Value (sym eq-T₂) v₂))
--               (begin
--                 subst id (sym eq-z2) (z (subst id eq-z z₁))
--               ≡⟨ dist-subst z eq-z (sym (trans (subst-preserves τ* (T₁ ⇒ T₂)) (congωl (λ η → ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η) (subst-to-env*-comp τ* (subst←RE ρ) [])))) (sym eq-z2) z₁ ⟩
--                 cong (λ f → f z₁) (subst-irrelevant {F = id} eq-1 eq-2 z)
--               )
--               lrv-t2-v′

-- LRVsubst (`∀α l , T) ρ τ* v z (e , v≡Λe , F) =
--   let eqᵢ = begin
--              Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T
--             ≡⟨ refl ⟩
--              Tsub (Tliftₛ (τ* ∘ₛₛ subst←RE ρ) l) T
--             ≡˘⟨ assoc-sub↑-sub↑ T τ*  (subst←RE ρ) ⟩
--               Tsub (Tliftₛ (subst←RE ρ) l) (Tsub (Tliftₛ τ* l) T)
--             ∎ in
--   let eqₒ = sym (cong (`∀α_,_ l) (assoc-sub↑-sub↑ T τ* (subst←RE ρ))) in
--   let sub₁ = subst Value eqₒ in
--   subst (Expr (l ∷ []) (l ◁* ∅)) eqᵢ e ,
--   (begin
--     sub₁ v
--   ≡⟨ cong sub₁ v≡Λe ⟩
--     sub₁ (Λ l ⇒ e)
--   ≡⟨ subst-split-Λ eqₒ eqᵢ e ⟩
--     Λ l ⇒ subst (Expr (l ∷ []) (l ◁* ∅)) eqᵢ e
--   ∎) , 
--   λ T′ R → F T′ R |> λ where
--     (vT[T′] , e[T′]⇓vT[T′] , lrv-t-ρ′) →
--       let eqᵥ = (cong (Tsub (Textₛ Tidₛ T′)) (sym (assoc-sub↑-sub↑ T τ* (subst←RE ρ)))) in
--       let subᵥ = subst Value eqᵥ in
--       subᵥ vT[T′] ,
--       let r = subst-split-⇓₂ eqᵥ e[T′]⇓vT[T′] in
--       subst id
--             (cong (_⇓ subᵥ vT[T′])
--               (sym (dist-subst' {F = Expr _ _} {G = Value} (_[ T′ ]T) (λ e′ → e′ [ T′ ]ET) eqᵢ eqᵥ e )))
--             r
--       ,
--       let eq-vtt = (begin
--                      (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T)
--                    ≡⟨ σ↑T[T′]≡TextₛσT′T (subst←RE (Tsub-act τ* ρ)) T′ T ⟩
--                      Tsub (Textₛ (subst←RE (Tsub-act τ* ρ)) T′) T
--                    ≡˘⟨ cong (λ σ → Tsub σ T) (subst←RE-ext-ext (Tsub-act τ* ρ) T′ R) ⟩
--                      Tsub (subst←RE (REext (Tsub-act τ* ρ) (T′ , R))) T
--                    ≡⟨ congωl (λ ρ → Tsub (subst←RE ρ) T) (Tsub-act-REext ρ τ* T′ R) ⟩
--                      Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T
--                    ∎) in
--       let lrv = LRVsubst T
--                          (REext ρ (T′ , R))
--                          (Tliftₛ τ* l)
--                          (subst Value eq-vtt vT[T′])
--                          (substω ⟦ T ⟧ (congωω (⟦ T′ ⟧ [] ∷_)
--                                          (conglω (λ σ → subst-to-env* σ [])
--                                            (trans
--                                              (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
--                                              (congωl (λ ρ → Tdropₛ (subst←RE ρ)) (Tsub-act-REext ρ τ* T′ R)))))
--                                        (z (⟦ T′ ⟧ [])))
--                          (dep-substωll (𝓥⟦ T ⟧)
--                                        (Tsub-act-REext ρ τ* T′ R)
--                                        (trans
--                                          (substω-∘ Value (λ ρ → Tsub (subst←RE ρ) T) (Tsub-act-REext ρ τ* T′ R))
--                                          (trans
--                                            (subst-subst {P = Value} (lemma1 (Tsub-act τ* ρ) T T′ R) {y≡z = (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R))})
--                                            (subst-irrelevant (trans (lemma1 (Tsub-act τ* ρ) T T′ R)
--                                                                     (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R)))
--                                                              (begin
--                                                                step-≡ (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T)
--                                                                (step-≡˘ (Tsub (Textₛ (subst←RE (Tsub-act τ* ρ)) T′) T)
--                                                                (step-≡ (Tsub (subst←RE (REext (Tsub-act τ* ρ) (T′ , R))) T)
--                                                                (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
--                                                                (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R)))
--                                                                (cong (λ σ → Tsub σ T) (subst←RE-ext-ext (Tsub-act τ* ρ) T′ R)))
--                                                                (σ↑T[T′]≡TextₛσT′T (subst←RE (Tsub-act τ* ρ)) T′ T))
--                                                              vT[T′])))
--                                        (trans
--                                          (substω-∘ (λ{ (σ₀ , σ) → ⟦ T ⟧ (⟦ σ₀ ⟧ [] ∷ subst-to-env* σ [])}) (λ ρ → let σ = subst←RE ρ in (σ l here , Tdropₛ σ)) (Tsub-act-REext ρ τ* T′ R))
--                                          (trans
--                                            (subst-∘ {P = id}{f = (λ { (σ₀ , σ) → ⟦ T ⟧ (⟦ σ₀ ⟧ [] ∷ subst-to-env* σ []) })}
--                                                     (congωl (λ ρ₁ → subst←RE ρ₁ l here , Tdropₛ (subst←RE ρ₁)) (Tsub-act-REext ρ τ* T′ R)))
--                                            (trans
--                                              (subst-irrelevant (cong (λ { (σ₀ , σ) → ⟦ T ⟧ (⟦ σ₀ ⟧ [] ∷ subst-to-env* σ []) })
--                                                                (congωl (λ ρ₁ → subst←RE ρ₁ l here , Tdropₛ (subst←RE ρ₁))
--                                                                (Tsub-act-REext ρ τ* T′ R)))
--                                                                (congωl ⟦ T ⟧
--                                                                  (congωω (⟦ T′ ⟧ [] ∷_)
--                                                                    (conglω (λ σ → subst-to-env* σ [])
--                                                                      (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
--                                                                        (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁)) (Tsub-act-REext ρ τ* T′ R))))))
--                                                                (z (⟦ T′ ⟧ [])))
--                                              (sym (substω-∘ id ⟦ T ⟧ (congωω (⟦ T′ ⟧ [] ∷_)
--                                                                      (conglω (λ σ → subst-to-env* σ [])
--                                                                        (trans (subst←RE-drop-ext (REext (Tsub-act τ* ρ) (T′ , R)))
--                                                                               (congωl (λ ρ₁ → Tdropₛ (subst←RE ρ₁))
--                                                                                       (Tsub-act-REext ρ τ* T′ R))))))))))
--                                        lrv-t-ρ′) in
--       subst₂ (𝓥⟦ Tsub (Tliftₛ τ* l) T ⟧ (REext ρ (T′ , R)))
--              (trans (subst-subst {P = Value} (begin
--                                                 step-≡ (Tsub (Tliftₛ (subst←RE (Tsub-act τ* ρ)) l) T [ T′ ]T)
--                                                 (step-≡˘ (Tsub (Textₛ (subst←RE (Tsub-act τ* ρ)) T′) T)
--                                                  (step-≡ (Tsub (subst←RE (REext (Tsub-act τ* ρ) (T′ , R))) T)
--                                                   (Tsub (subst←RE (Tsub-act (Tliftₛ τ* l) (REext ρ (T′ , R)))) T ∎)
--                                                   (congωl (λ ρ₁ → Tsub (subst←RE ρ₁) T) (Tsub-act-REext ρ τ* T′ R)))
--                                                  (cong (λ σ → Tsub σ T) (subst←RE-ext-ext (Tsub-act τ* ρ) T′ R)))
--                                                 (σ↑T[T′]≡TextₛσT′T (subst←RE (Tsub-act τ* ρ)) T′ T))
--                                               {y≡z = (sym (assoc-sub-sub T (Tliftₛ τ* l) (subst←RE (REext ρ (T′ , R)))))})
--                      (trans
--                        (subst-irrelevant {F = Value} _ _ vT[T′])
--                        (sym (subst-subst {P = Value} (cong (Tsub (Textₛ Tidₛ T′)) (sym (assoc-sub↑-sub↑ T τ* (subst←RE ρ))))
--                                                      {y≡z = (lemma1 ρ (Tsub (Tliftₛ τ* l) T) T′ R)}))))
--              {!!}
--              lrv 

-- LRVsubst `ℕ ρ τ* v z (n , v≡#n , n≡z) =
--   n ,
--   v≡#n ,
--   trans n≡z (sym (subst-id id _))

-- LRVsubst′ T ρ τ* v z x = {!!}
