{-# OPTIONS --allow-unsolved-metas #-}
module ExprSubstProperties where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_])
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst; subst-sym-subst; sym-cong;
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
module R = H.≅-Reasoning

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution

-- equality utils

sym-trans : ∀ {ℓ} {A : Set ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) → sym (trans p q) ≡ trans (sym q) (sym p)
sym-trans refl refl = refl

trans-assoc : ∀ {ℓ} {A : Set ℓ} {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → trans p (trans q r) ≡ trans (trans p q) r
trans-assoc refl refl refl = refl

trans-idʳ : ∀ {ℓ} {A : Set ℓ} {a b : A} (p : a ≡ b) → trans p refl ≡ p
trans-idʳ refl = refl

trans-idˡ : ∀ {ℓ} {A : Set ℓ} {a b : A} (p : a ≡ b) → trans refl p ≡ p
trans-idˡ refl = refl


-- splitting substitutions

subst-split-ƛ : 
    ∀ {Δ}{Γ : TEnv Δ}
  → {t₁ t₁′ : Type Δ l₁}
  → {t₂ t₂′ : Type Δ l₂}
  → (eq : t₁ ⇒ t₂ ≡ t₁′ ⇒ t₂′)
  → (eq₁ : t₁ ≡ t₁′)
  → (eq₂ : t₂ ≡ t₂′)
  → (a : Expr Δ (t₁ ◁ Γ) t₂)
  → subst (Expr Δ Γ) eq (ƛ a) ≡ ƛ subst₂ (λ T₁ T₂ → Expr Δ (T₁ ◁ Γ) T₂) eq₁ eq₂ a
subst-split-ƛ refl refl refl a = refl

subst-split-ƛ-∅ : 
    ∀ {t₁ t₁′ : Type [] l₁}
  → {t₂ t₂′ : Type [] l₂}
  → (eq : t₁ ⇒ t₂ ≡ t₁′ ⇒ t₂′)
  → (eq₁ : t₁ ≡ t₁′)
  → (eq₂ : t₂ ≡ t₂′)
  → (a : Expr [] (t₁ ◁ ∅) t₂)
  → subst (Expr [] ∅) eq (ƛ a) ≡ ƛ subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ a
subst-split-ƛ-∅ refl refl refl a = refl

subst-split-Λ :
  ∀ {Δ}{Γ : TEnv Δ}
  → {tᵢ tᵢ′ : Type (l ∷ Δ) l₁}
  → (eqₒ : `∀α l , tᵢ ≡ `∀α l , tᵢ′)
  → (eqᵢ : tᵢ ≡ tᵢ′)
  → (a : Expr (l ∷ Δ) (l ◁* Γ) tᵢ)
  → subst (Expr Δ Γ) eqₒ (Λ l ⇒ a) ≡ Λ l ⇒ subst (Expr (l ∷ Δ) (l ◁* Γ)) eqᵢ a
subst-split-Λ refl refl a = refl

subst-split-Λ-∅ :
  ∀ {tᵢ tᵢ′ : Type [ l ] l₁}
  → (eqₒ : `∀α l , tᵢ ≡ `∀α l , tᵢ′)
  → (eqᵢ : tᵢ ≡ tᵢ′)
  → (a : Expr [ l ] (l ◁* ∅) tᵢ)
  → subst (Expr [] ∅) eqₒ (Λ l ⇒ a) ≡ Λ l ⇒ subst (Expr [ l ] (l ◁* ∅)) eqᵢ a
subst-split-Λ-∅ refl refl a = refl

subst-split-· : ∀ {l₁ l₂} {T₁ T₁′ : Type Δ l₁}{T₂ T₂′ : Type Δ l₂}
  → (eq : T₁ ⇒ T₂ ≡ T₁′ ⇒ T₂′)
  → (eq₁ : T₁ ≡ T₁′)
  → (eq₂ : T₂ ≡ T₂′)
  → (e₁ : Expr Δ Γ (T₁ ⇒ T₂)) (e₂ : Expr Δ Γ T₁)
  → subst (Expr _ _) eq e₁ · subst (Expr _ _) eq₁ e₂ ≡ subst (Expr _ _) eq₂ (e₁ · e₂)
subst-split-· refl refl refl e₁ e₂ = refl

subst₂-subst-subst′ : ∀ {l la lb}
  → {A : Set la} {B : Set lb}
  → {a₁ a₂ : A} {b₁ b₂ : B}
  → (F : A → B → Set l)
  → (eq₁ : a₁ ≡ a₂)
  → (eq₂ : b₁ ≡ b₂)
  → (x : F a₁ b₁)
  → subst (λ b → F a₂ b) eq₂ (subst (λ a → F a b₁) eq₁ x) ≡ subst₂ F eq₁ eq₂ x
subst₂-subst-subst′ F refl refl x = refl

subst₂-subst-subst″ : ∀ {l la lb}
  → {A : Set la} {B : Set lb}
  → {a₁ a₂ : A} {b₁ b₂ : B}
  → (F : A → B → Set l)
  → (eq₁ : a₁ ≡ a₂)
  → (eq₂ : b₁ ≡ b₂)
  → (x : F a₁ b₁)
  → (subst (λ a → F a b₂) eq₁ (subst (λ b → F a₁ b) eq₂ x)) ≡ subst₂ F eq₁ eq₂ x
subst₂-subst-subst″ F refl refl x = refl

cong-const : ∀ {a b} {A : Set a}{B : Set b} {x y : A} {K : B} (eq : x ≡ y) → cong (λ z → K) eq ≡ refl
cong-const refl = refl



-- single substitution dissected

sub0 : Expr Δ Γ (Tsub Tidₛ T₁) → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0 e′ = Eextₛ Tidₛ Eidₛ e′

sub0′ : Expr Δ Γ T₁ → ESub Tidₛ (T₁ ◁ Γ) Γ
sub0′ e′ = Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T _)) e′)

-- general equality of expression substitutions

_~_ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → Set
_~_ {Δ₁ = Δ₁} {Γ₁ = Γ₁} σ₁ σ₂ = ∀ l (T : Type Δ₁ l) → (x : inn T Γ₁) → σ₁ l T x ≡ σ₂ l T x

~-lift : ∀ {l} {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → Eliftₛ {T = T} σ* σ₁ ~ Eliftₛ σ* σ₂
~-lift σ₁ σ₂ σ₁~σ₂ l T here = refl
~-lift σ₁ σ₂ σ₁~σ₂ l T (there x) = cong Ewk (σ₁~σ₂ l T x)

~-lift* : ∀ {l : Level} {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (Eliftₛ-l {l = l} σ* σ₁) ~ Eliftₛ-l σ* σ₂
~-lift* σ₁ σ₂ σ₁~σ₂ l _ (tskip x) rewrite σ₁~σ₂ l _ x = refl


Esub~ : {σ* : TSub Δ₁ Δ₂} → (σ₁ σ₂ : ESub σ* Γ₁ Γ₂) → σ₁ ~ σ₂ → (e : Expr Δ₁ Γ₁ T) → Esub σ* σ₁ e ≡ Esub σ* σ₂ e
Esub~ σ₁ σ₂ σ₁~σ₂ (# n) = refl
Esub~ σ₁ σ₂ σ₁~σ₂ (` x) = σ₁~σ₂ _ _ x
Esub~ σ₁ σ₂ σ₁~σ₂ (ƛ e) = cong ƛ_ (Esub~ _ _ (~-lift σ₁ σ₂ σ₁~σ₂) e)
Esub~ σ₁ σ₂ σ₁~σ₂ (e · e₁) = cong₂ _·_ (Esub~ σ₁ σ₂ σ₁~σ₂ e) (Esub~ σ₁ σ₂ σ₁~σ₂ e₁)
Esub~ σ₁ σ₂ σ₁~σ₂ (Λ l ⇒ e) = cong (Λ l ⇒_) (Esub~ _ _ (~-lift* {l = l} σ₁ σ₂ σ₁~σ₂) e)
Esub~ σ₁ σ₂ σ₁~σ₂ (e ∙ T′) rewrite Esub~ σ₁ σ₂ σ₁~σ₂ e = refl


-- general lax equality of expression substitutions

_~[_]~_ : {σ*₁ σ*₂ : TSub Δ₁ Δ₂} → (σ₁ : ESub σ*₁ Γ₁ Γ₂) (eqσ : σ*₁ ≡ σ*₂) (σ₂ : ESub σ*₂ Γ₁ Γ₂) → Set
_~[_]~_ {Δ₁ = Δ₁}{Δ₂ = Δ₂}{Γ₁ = Γ₁}{Γ₂ = Γ₂} σ₁ eqσ σ₂ =
  ∀ l (T : Type Δ₁ l) → (x : inn T Γ₁)
  → σ₁ l T x ≡ subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (sym eqσ)) (σ₂ l T x)


Esub~~ : {σ*₁ σ*₂ : TSub Δ₁ Δ₂} → (eqσ : σ*₁ ≡ σ*₂) (σ₁ : ESub σ*₁ Γ₁ Γ₂) (σ₂ : ESub σ*₂ Γ₁ Γ₂) → σ₁ ~[ eqσ ]~ σ₂ → (e : Expr Δ₁ Γ₁ T)
  → Esub σ*₁ σ₁ e ≡ subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (sym eqσ)) (Esub σ*₂ σ₂ e)
Esub~~ refl σ₁ σ₂ ~~ e = Esub~ σ₁ σ₂ ~~ e


--- want to prove
--- Goal: Esub σ* (Eextₛ σ* σ e′) e
---     ≡ (Esub σ* (Eliftₛ σ* σ) e) [ e′ ]E
---
--- at the level of substitutions
---
---     (Eextₛ σ* σ e′) ~  (Eliftₛ σ* σ) >>SS sub0 e′

-- TODO: not necessary with Heterogeneous equality
subst-`-lem : ∀ {Γ : TEnv Δ} {T T′ : Type Δ l} (eq₁ : (T ◁ Γ) ≡ (T′ ◁ Γ)) (eq₂ : T ≡ T′) →
    (` here) ≡ subst (λ Γ → Expr _ Γ T′) eq₁ (subst (λ T′′ → Expr _ (T ◁ Γ) T′′) eq₂ (` here))
subst-`-lem refl refl = refl

-- TODO: not necessary with Heterogeneous equality
subst-`-lem₂ :
  ∀ {Γ : TEnv Δ} {T U V W : Type Δ l} {T′ U′ : Type Δ l₁}
    (eq₁ : V ≡ U) (eq₂ : W ≡ V) (eq₃ : T ≡ W) (eq₄ : T ≡ U) (eq₅ : (T′ ◁ Γ) ≡ (U′ ◁ Γ))
    (x : inn T Γ) →
  let sub₁ = subst (Expr _ (U′ ◁ Γ)) eq₁ in
  let sub₃ = subst (Expr _ (U′ ◁ Γ)) eq₂ in
  let sub₅' = subst (Expr _ (U′ ◁ Γ)) eq₃ in
  let sub₅ = subst (Expr _ (T′ ◁ Γ)) eq₄ in
  let sub₆ = subst (λ Γ → Expr _ Γ U) eq₅ in
  sub₁ (sub₃ (sub₅' (` there x))) ≡ sub₆ (sub₅ (` there x))
subst-`-lem₂ refl refl refl refl refl x = refl

EliftₛEidₛ≡Eidₛ : ∀ {T : Type Δ l}{Γ : TEnv Δ}
  → Eliftₛ {Γ₁ = Γ}{Γ₂ = Γ} {T = T} Tidₛ Eidₛ ~ subst (ESub Tidₛ (T ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T))) (Eidₛ {Γ  = T ◁ Γ})
EliftₛEidₛ≡Eidₛ {Γ = Γ} l T here =
  let
    F₁ = (λ Γ → Expr _ Γ (Tsub Tidₛ T)); E₁ = (cong (_◁ Γ) (sym (TidₛT≡T T))); sub₁ = subst F₁ E₁
    F₂ = (λ T′ → Expr _ (T ◁ Γ) T′);     E₂ = (sym (TidₛT≡T T));               sub₂ = subst F₂ E₂
    F₃ = (ESub Tidₛ (T ◁ Γ));            E₃ = (cong (_◁ Γ) (sym (TidₛT≡T T))); sub₃ = subst F₃ E₃
  in
  begin
    (` here)
  ≡⟨ subst-`-lem (cong (_◁ Γ) (sym (TidₛT≡T T))) (sym (TidₛT≡T T)) ⟩
    sub₁ (sub₂ (` here))
  ≡⟨⟩
    sub₁ (Eidₛ l T here)
  ≡⟨ sym (dist-subst' {F = F₃} {G = F₁} id (λ σ → σ l T here) E₃ E₁ Eidₛ ) ⟩
    (sub₃ Eidₛ) l T here
  ∎
EliftₛEidₛ≡Eidₛ {Γ = Γ} l T (there {T′ = T′} x) =
  let
    F₁ = (Expr _ (Tsub Tidₛ T′ ◁ Γ));    E₁ = (TidᵣT≡T (Tsub Tidₛ T));              sub₁ = subst F₁ E₁
    F₂ = (Expr _ Γ);                     E₂ = (sym (TidₛT≡T T));                    sub₂ = subst F₂ E₂
    F₃ = (Expr _ (Tsub Tidₛ T′ ◁ Γ));    E₃ = (cong (Tren Tidᵣ) (sym (TidₛT≡T T))); sub₃ = subst F₃ E₃
    F₄ = (λ T₁ → inn T₁ Γ);              E₄ = (sym (TidᵣT≡T T));                    sub₄ = subst F₄ E₄
    F₅ = (Expr _ (T′ ◁ Γ));              E₅ = (sym (TidₛT≡T T));                    sub₅ = subst F₅ E₅
    F₆ = (λ Γ → Expr _ Γ (Tsub Tidₛ T)); E₆ = (cong (_◁ Γ) (sym (TidₛT≡T T′)));     sub₆ = subst F₆ E₆
    F₇ = (ESub Tidₛ (T′ ◁ Γ));           E₇ = (cong (_◁ Γ) (sym (TidₛT≡T T′)));     sub₇ = subst F₇ E₇
    F₈ = (Expr _ (Tsub Tidₛ T′ ◁ Γ));    E₈ = (sym (TidᵣT≡T T));                    sub₈ = subst F₈ E₈                    
  in
  begin
    Eliftₛ {T = T′} Tidₛ Eidₛ l T (there x)
  ≡⟨⟩
    Ewk (Eidₛ _ _ x)
  ≡⟨⟩
    sub₁ (Eren _ (Ewkᵣ Tidᵣ Eidᵣ) (sub₂ (` x)))
  ≡⟨ cong (sub₁)
          (dist-subst' {F = F₂} {G = F₃} (Tren Tidᵣ) (Eren _ (Ewkᵣ Tidᵣ Eidᵣ)) E₂ E₃ (` x)) ⟩
    sub₁ (sub₃ (Eren _ (Ewkᵣ Tidᵣ Eidᵣ) (` x)))
  ≡⟨⟩
    sub₁ (sub₃ (` there (sub₄ x)))
  ≡⟨ cong (λ ■ → sub₁ (sub₃ ■))
          (dist-subst' {F = F₄} {G = F₈} id (λ x → ` there x) E₄ E₈ x) ⟩
    sub₁ (sub₃ (sub₈ (` there x)))
  ≡⟨ subst-`-lem₂ E₁ E₃ E₈ E₅ E₆ x ⟩
    sub₆ (sub₅ (` there x))
  ≡⟨⟩
    sub₆ (Eidₛ l T (there x))
  ≡⟨ sym (dist-subst' {F = F₇} {G = F₆} id (λ σ → σ l T (there x)) E₇ E₆ Eidₛ ) ⟩
    (sub₇ Eidₛ) l T (there x)
  ∎

Eliftₛ-lEidₛ≡Eidₛ : ∀ {Γ : TEnv Δ}{l} →
  Eliftₛ-l {Γ₁ = Γ}{l = l} Tidₛ Eidₛ ~ subst (λ τ → ESub τ (l ◁* Γ) (l ◁* Γ)) (sym (TliftₛTidₛ≡Tidₛ Δ l)) (Eidₛ {Γ = l ◁* Γ})
Eliftₛ-lEidₛ≡Eidₛ{Δ = Δ} {Γ = Γ} {l = l} l′ .(Twk _) (tskip {T = T} x) =
  let
    F₁ = (Expr (l ∷ Δ) (l ◁* Γ))          ; E₁ = (sym (swap-Tsub-Twk Tidₛ T))    ; sub₁ = subst F₁ E₁
    F₂ = (Expr _ _)                       ; E₂ = (sym (TidₛT≡T T))                ; sub₂ = subst F₂ E₂
    F₃ = (Expr _ _)                       ; E₃ = (cong Twk E₂)                    ; sub₃ = subst F₃ E₃
    F₄ = (Expr (l ∷ Δ) (l ◁* Γ))          ; E₄ = (trans E₃ E₁)                    ; sub₄ = subst F₄ E₄

    F₉ = (λ τ → ESub τ (l ◁* Γ) (l ◁* Γ)) ; E₉ = (sym (TliftₛTidₛ≡Tidₛ Δ l))      ; sub₉ = subst F₉ E₉
    F₈ = (λ τ → Expr (l ∷ Δ) (l ◁* Γ)
           (Tsub τ (Twk T)))              ; E₈ = (sym (TliftₛTidₛ≡Tidₛ Δ l))      ; sub₈ = subst F₈ E₈
    F₇ = (Expr (l ∷ Δ) (l ◁* Γ))          ; E₇ = (sym (TidₛT≡T (Twk T)))          ; sub₇ = subst F₇ E₇
    F₆ = (Expr (l ∷ Δ) (l ◁* Γ))          ; E₆ = (cong (λ τ → Tsub τ (Twk T)) E₈) ; sub₆ = subst F₆ E₆
    F₅ = (Expr (l ∷ Δ) (l ◁* Γ))          ; E₅ = (trans E₇ E₆)                    ; sub₅ = subst F₅ E₅
  in
  begin
    Eliftₛ-l Tidₛ Eidₛ l′ (Twk T) (tskip x)
  ≡⟨ refl ⟩
    sub₁ (Ewk-l (Eidₛ l′ T x))
  ≡⟨ refl ⟩
    sub₁ (Ewk-l (sub₂ (` x)))
  ≡⟨ cong sub₁ (dist-subst' {F = F₂} {G = F₃} Twk Ewk-l E₂ E₃ (` x)) ⟩
    sub₁ (sub₃ (Ewk-l (` x)))
  ≡⟨ refl ⟩
    sub₁ (sub₃ (` tskip x))
  ≡⟨ subst-subst {P = F₁} E₃ {E₁} {` tskip x} ⟩
    sub₄ (` tskip x)
  ≡⟨ subst-irrelevant E₄ E₅ (` tskip x) ⟩
    sub₅ (` tskip x)
  ≡⟨ sym (subst-subst {P = F₅} E₇ {E₆} {` tskip x}) ⟩
    sub₆ (sub₇ (` tskip x))
  ≡⟨ sym (subst-∘ {P = F₆} {f = λ τ → Tsub τ (Twk T)} E₈ {sub₇ (` tskip x)}) ⟩
    sub₈ (sub₇ (` tskip x))
  ≡⟨ refl ⟩
    sub₈ (Eidₛ l′ (Twk T) (tskip x))
  ≡⟨ sym (dist-subst' {F = F₉} {G = F₈} id (λ σ → σ l′ (Twk T) (tskip x)) E₉ E₈ Eidₛ) ⟩
    sub₉ Eidₛ l′ (Twk T) (tskip x)
  ∎

-- identity renaming

-- probably not needed

-- EliftᵣEidᵣ≡Eidᵣ : Eliftᵣ {Γ₁ = Γ}{T = T} Tidᵣ Eidᵣ ≡ {!Eidᵣ{Γ = T ◁ Γ}!}
-- EliftᵣEidᵣ≡Eidᵣ = {!Eliftᵣ!}

-- Eidᵣx≡x : ∀ {T : Type Δ l} (x : inn T Γ) → let rhs = subst (λ t → inn{l = l} t Γ) (sym (TidᵣT≡T _)) in Eidᵣ l T x ≡ rhs x
-- Eidᵣx≡x x = refl

-- Eidᵣe≡e : ∀ (e : Expr Δ Γ T) → Eren Tidᵣ Eidᵣ e ≡ subst (Expr _ _) (sym (TidᵣT≡T _)) e
-- Eidᵣe≡e (# n) = refl
-- Eidᵣe≡e {Γ = Γ} (`_ {l = l} x) =
--   begin
--     Eren Tidᵣ Eidᵣ (` x)
--   ≡⟨ refl ⟩
--     (` subst (λ t → inn t Γ) (sym (TidᵣT≡T _)) x)
--   ≡⟨ dist-subst' {F = (λ t → inn t Γ)} {G = Expr _ _} id `_ (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) x ⟩
--     subst (Expr _ _) (sym (TidᵣT≡T _)) (` x)
--   ∎
-- Eidᵣe≡e (ƛ e) =
--   begin
--     Eren Tidᵣ Eidᵣ (ƛ e)
--   ≡⟨ refl ⟩
--     (ƛ Eren Tidᵣ (Eliftᵣ Tidᵣ Eidᵣ) e)
--   ≡⟨ cong ƛ_ {!subst₂-subst-subst′ (λ T T′ → Expr _ (T′ ◁ _) T) (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) e!} ⟩
--     {!!}
--   ≡⟨ cong ƛ_ {!subst₂-subst-subst′ (λ T T′ → Expr _ (T′ ◁ _) T) (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) e!} ⟩
--     (ƛ subst₂ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) e)
--   ≡⟨ sym (subst-split-ƛ (sym (TidᵣT≡T (_ ⇒ _))) (sym (TidᵣT≡T _)) (sym (TidᵣT≡T _)) e) ⟩
--     subst (Expr _ _) (sym (TidᵣT≡T (_ ⇒ _))) (ƛ e)
--   ∎
-- Eidᵣe≡e (e₁ · e₂) = {!!}
-- Eidᵣe≡e (Λ l ⇒ e) = {!!}
-- Eidᵣe≡e (e ∙ T′) = {!!}

-- identity substitution

Eidₛx≡x : ∀ {T : Type Δ l} (x : inn T Γ) → Esub Tidₛ Eidₛ (` x) ≡ subst (Expr _ _) (sym (TidₛT≡T _)) (` x)
Eidₛx≡x {T = T} x rewrite TidₛT≡T T = refl

Eidₛe≡e : ∀ (e : Expr Δ Γ T) → Esub Tidₛ Eidₛ e ≡ subst (Expr _ _) (sym (TidₛT≡T _)) e
Eidₛe≡e (# n) = refl
Eidₛe≡e {T = T} (` x) rewrite TidₛT≡T T = refl
Eidₛe≡e {Γ = Γ} {T = _⇒_ {l = l} T₁ T₂} (ƛ e) =
  let
    context : {T : Type _ l} → (σ : ESub Tidₛ (T₁ ◁ Γ) (T ◁ Γ)) → Expr _ (T ◁ Γ) (Tsub Tidₛ T₂)
    context = λ {T : Type _ l} σ → Esub{Γ₂ = T ◁ Γ} Tidₛ σ e
    subst-Eidₛ : ESub Tidₛ (T₁ ◁ Γ) (Tsub Tidₛ T₁ ◁ Γ)
    subst-Eidₛ = (subst (ESub Tidₛ (T₁ ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T₁))) Eidₛ)
  in
  begin
    Esub Tidₛ Eidₛ (ƛ e)
  ≡⟨⟩
    (ƛ Esub Tidₛ (Eliftₛ Tidₛ Eidₛ) e)
  ≡⟨ cong ƛ_ (begin
               Esub Tidₛ (Eliftₛ Tidₛ Eidₛ) e
             ≡⟨ Esub~ (Eliftₛ Tidₛ Eidₛ) (subst (ESub Tidₛ (T₁ ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T₁))) Eidₛ) EliftₛEidₛ≡Eidₛ e ⟩
               Esub Tidₛ (subst (ESub Tidₛ (T₁ ◁ Γ)) (cong (_◁ Γ) (sym (TidₛT≡T T₁))) Eidₛ) e
             ≡⟨ sym (cong context (subst-∘ {P = ESub Tidₛ (T₁ ◁ Γ)} {f = _◁ Γ} (sym (TidₛT≡T T₁)) {Eidₛ})) ⟩
               Esub Tidₛ
                  (subst (λ T → ESub Tidₛ (T₁ ◁ Γ) (T ◁ Γ)) (sym (TidₛT≡T T₁))
                   Eidₛ)
                  e
             ≡⟨ dist-subst' {G = (λ T′ → Expr _ (T′ ◁ Γ) (Tsub Tidₛ T₂))}
                             id
                             context
                             (sym (TidₛT≡T T₁))
                             (sym (TidₛT≡T T₁))
                             Eidₛ ⟩
                subst (λ T′ → Expr _ (T′ ◁ Γ) (Tsub Tidₛ T₂)) (sym (TidₛT≡T T₁)) (context Eidₛ)
             ≡⟨ refl ⟩
                subst (λ T′ → Expr _ (T′ ◁ Γ) (Tsub Tidₛ T₂)) (sym (TidₛT≡T T₁)) (Esub Tidₛ Eidₛ e)
             ≡⟨ cong
                  (subst (λ T′ → Expr _ (T′ ◁ Γ) (Tsub Tidₛ T₂)) (sym (TidₛT≡T T₁)))
                  (Eidₛe≡e e) ⟩
               subst (λ T′ → Expr _ (T′ ◁ Γ) (Tsub Tidₛ T₂)) (sym (TidₛT≡T T₁))
                 (subst (Expr _ (T₁ ◁ Γ)) (sym (TidₛT≡T T₂)) e)
             ≡⟨ subst₂-subst-subst″ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidₛT≡T _)) (sym (TidₛT≡T _)) e ⟩
               subst₂ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidₛT≡T _)) (sym (TidₛT≡T _))
                 e
             ∎) ⟩
    (ƛ
      subst₂ (λ T₁ → Expr _ (T₁ ◁ _)) (sym (TidₛT≡T _)) (sym (TidₛT≡T _))
      e)
  ≡⟨ sym (subst-split-ƛ (sym (TidₛT≡T (_ ⇒ _))) (sym (TidₛT≡T _)) (sym (TidₛT≡T _)) e ) ⟩
    subst (Expr _ _) (sym (TidₛT≡T (_ ⇒ _))) (ƛ e)
  ∎
Eidₛe≡e (e₁ · e₂) =
  begin
    Esub Tidₛ Eidₛ (e₁ · e₂)
  ≡⟨⟩
    (Esub Tidₛ Eidₛ e₁ · Esub Tidₛ Eidₛ e₂)
  ≡⟨ cong₂ _·_ (Eidₛe≡e e₁) (Eidₛe≡e e₂) ⟩
    (subst (Expr _ _) (sym (TidₛT≡T (_ ⇒ _))) e₁ ·
      subst (Expr _ _) (sym (TidₛT≡T _)) e₂)
  ≡⟨ subst-split-· (sym (TidₛT≡T (_ ⇒ _))) (sym (TidₛT≡T _)) (sym (TidₛT≡T _)) e₁ e₂ ⟩
    subst (Expr _ _) (sym (TidₛT≡T _)) (e₁ · e₂)
  ∎
-- TliftₛTidₛ≡Tidₛ
Eidₛe≡e {Γ = Γ} (Λ_⇒_ {l′ = l′} l {T} e) =
  let context = λ {τ} σ → Esub {Γ₂ = l ◁* Γ} τ σ e in
  begin
    Esub Tidₛ Eidₛ (Λ l ⇒ e)
  ≡⟨ refl ⟩
    (Λ l ⇒ Esub (Tliftₛ Tidₛ l) (Eliftₛ-l Tidₛ Eidₛ) e)
  ≡⟨ cong (Λ l ⇒_)
     (Esub~ (Eliftₛ-l Tidₛ Eidₛ)
            (subst (λ τ → ESub τ (l ◁* Γ) (l ◁* Γ)) (sym (TliftₛTidₛ≡Tidₛ _ l)) Eidₛ)
            Eliftₛ-lEidₛ≡Eidₛ
            e) ⟩
   (Λ l ⇒
     Esub (Tliftₛ Tidₛ l)
     (subst (λ τ → ESub τ (l ◁* Γ) (l ◁* Γ)) (sym (TliftₛTidₛ≡Tidₛ _ l)) 
        Eidₛ)
     e)
  ≡⟨ cong (Λ l ⇒_)
    (dist-subst' {F = (λ τ → ESub τ (l ◁* Γ) (l ◁* Γ))}
                 {G = Expr (l ∷ _) (l ◁* _)}
                 (λ τ → Tsub τ T)
                 context
                 (sym (TliftₛTidₛ≡Tidₛ _ l))
                 (cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l)))
                 Eidₛ) ⟩
    (Λ l ⇒
      subst (Expr (l ∷ _) (l ◁* Γ))
      (cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l)))
      (Esub Tidₛ Eidₛ e))
  ≡⟨ cong (Λ l ⇒_) (cong
                      (subst (Expr (l ∷ _) (l ◁* _))
                       (cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l))))
                      (Eidₛe≡e e)) ⟩
    (Λ l ⇒
      subst (Expr (l ∷ _) (l ◁* _))
      (cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l)))
      (subst (Expr (l ∷ _) (l ◁* _)) (sym (TidₛT≡T T)) e))
  ≡⟨ cong (Λ l ⇒_) (subst-subst {P = (Expr (l ∷ _) (l ◁* _))}
                                (sym (TidₛT≡T T))
                                {(cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l)))}
                                {e}) ⟩
    (Λ l ⇒
      subst (Expr (l ∷ _) (l ◁* _))
      (trans (sym (TidₛT≡T T))
       (cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l))))
      e)
  ≡⟨ sym (subst-split-Λ (sym (TidₛT≡T (`∀α l , _)))
                         (trans (sym (TidₛT≡T T)) (cong (λ τ → Tsub τ T) (sym (TliftₛTidₛ≡Tidₛ _ l))))
                         e) ⟩
    subst (Expr _ _) (sym (TidₛT≡T (`∀α l , _))) (Λ l ⇒ e)
  ∎
Eidₛe≡e {Γ = Γ} (_∙_ {l = l′}{l′ = l}{T = T} e  T′) =
  let
    subst-e : Expr _ Γ (`∀α l′ , Tsub (Tliftₛ Tidₛ _) T)
    subst-e = subst (Expr _ Γ) (sym (TidₛT≡T (`∀α l′ , T))) e
    context : ∀ {T : Type _ l} → Expr _ Γ (`∀α l′ , T) → Expr _ Γ (T [ T′ ]T)
    context = _∙ T′
  in
  begin
    Esub Tidₛ Eidₛ (e ∙ T′)
  ≡⟨ refl ⟩
    subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
      (Esub Tidₛ Eidₛ e ∙ Tsub Tidₛ T′)
  ≡⟨ cong (subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′)))
     (sym (dcong (Esub Tidₛ Eidₛ e ∙_) (sym (TidₛT≡T T′)))) ⟩
     subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
       (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T))
        (sym (TidₛT≡T T′))
        (Esub Tidₛ Eidₛ e ∙ T′))
  ≡⟨ cong (subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′)))
      (cong (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T)) (sym (TidₛT≡T T′)))
        (cong (_∙ T′) (Eidₛe≡e e))) ⟩
    subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
      (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T))
       (sym (TidₛT≡T T′))
       (context (subst (Expr _ Γ) (sym (TidₛT≡T (`∀α l′ , T))) e)))
  ≡⟨ cong (subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′)))
     (cong (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T)) (sym (TidₛT≡T T′)))
       (cong (λ H → (subst (Expr _ Γ) H e ∙ T′))
         (sym-cong {f = (`∀α_,_ l′)} (trans (cong (λ σ → Tsub σ T) (TliftₛTidₛ≡Tidₛ _ l′)) (TidₛT≡T T))))) ⟩
    subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
      (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ l′) T [ z ]T))
       (sym (TidₛT≡T T′))
       (subst (Expr _ Γ)
        (cong (`∀α_,_ l′)
         (sym
          (trans (cong (λ σ → Tsub σ T) (TliftₛTidₛ≡Tidₛ _ l′))
           (TidₛT≡T T))))
        e
        ∙ T′))
  ≡⟨ cong (subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′)))
     (cong (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T)) (sym (TidₛT≡T T′)))
       (cong (_∙ T′) (sym (subst-∘ {P = Expr _ Γ} {f = `∀α_,_ l′} (sym (trans (cong (λ σ → Tsub σ T) (TliftₛTidₛ≡Tidₛ _ l′)) (TidₛT≡T T))) {e})))) ⟩
    subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
      (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ l′) T [ z ]T))
       (sym (TidₛT≡T T′))
       (subst (Expr _ Γ ∘ `∀α_,_ l′)
        (sym
         (trans (cong (λ σ → Tsub σ T) (TliftₛTidₛ≡Tidₛ _ l′)) (TidₛT≡T T)))
        e
        ∙ T′))
  ≡⟨ cong (subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′)))
     (cong (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T)) (sym (TidₛT≡T T′)))
       (dist-subst' {F = (λ T → Expr _ Γ (`∀α l′ , T))}
                    {G = Expr _ Γ}
                    (_[ T′ ]T)
                    context
                    (sym (trans (cong (λ σ → Tsub σ T) (TliftₛTidₛ≡Tidₛ _ l′)) (TidₛT≡T T)))
                    (T[T′]T≡Tidₛ↑T[T′]T T T′)
                    e)) ⟩
    subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
      (subst (λ z → Expr _ Γ (Tsub (Tliftₛ Tidₛ _) T [ z ]T)) (sym (TidₛT≡T T′))
        (subst (Expr _ Γ) (T[T′]T≡Tidₛ↑T[T′]T T T′) (context e)))
  ≡⟨ cong (subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′)))
     (subst-∘ {P = Expr _ Γ} {f = λ T′ → (Tsub (Tliftₛ Tidₛ l′) T [ T′ ]T)} (sym (TidₛT≡T T′)) ) ⟩
    subst (Expr _ Γ) (sym (swap-Tsub-[] Tidₛ T T′))
      (subst (Expr _ Γ) (cong (λ T′₁ → Tsub (Tliftₛ Tidₛ l′) T [ T′₁ ]T) (sym (TidₛT≡T T′)))
       (subst (Expr _ Γ) (T[T′]T≡Tidₛ↑T[T′]T T T′) (e ∙ T′)))
  ≡⟨ subst-subst {P = Expr _ Γ} (cong (λ T′₁ → Tsub (Tliftₛ Tidₛ l′) T [ T′₁ ]T) (sym (TidₛT≡T T′))) {sym (swap-Tsub-[] Tidₛ T T′)}  ⟩
    subst (Expr _ Γ)
      (trans
       (cong (λ T′₁ → Tsub (Tliftₛ Tidₛ l′) T [ T′₁ ]T)
        (sym (TidₛT≡T T′)))
       (sym (swap-Tsub-[] Tidₛ T T′)))
      (subst (Expr _ Γ) (T[T′]T≡Tidₛ↑T[T′]T T T′) (e ∙ T′))
  ≡⟨ subst-subst {P = Expr _ Γ} (T[T′]T≡Tidₛ↑T[T′]T T T′) {trans
       (cong (λ T′₁ → Tsub (Tliftₛ Tidₛ l′) T [ T′₁ ]T)
        (sym (TidₛT≡T T′)))
       (sym (swap-Tsub-[] Tidₛ T T′))} ⟩
    subst (Expr _ Γ)
      (trans (T[T′]T≡Tidₛ↑T[T′]T T T′)
       (trans
        (cong (λ T′₁ → Tsub (Tliftₛ Tidₛ l′) T [ T′₁ ]T)
         (sym (TidₛT≡T T′)))
        (sym (swap-Tsub-[] Tidₛ T T′))))
      (e ∙ T′)
  ≡⟨ subst-irrelevant _ (sym (TidₛT≡T (T [ T′ ]T))) (e ∙ T′) ⟩
    subst (Expr _ _) (sym (TidₛT≡T (T [ T′ ]T))) (e ∙ T′)
  ∎


-- composition of expression substitutions and renamings

_>>SR_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ* Γ₁ Γ₂ → ERen ρ* Γ₂ Γ₃ → ESub (σ* ∘ₛᵣ ρ*) Γ₁ Γ₃
_>>SR_ {Δ₃ = Δ₃}{σ* = σ*}{ρ* = ρ*}{Γ₃ = Γ₃} σ ρ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-ren-sub T σ* ρ*) (Eren ρ* ρ (σ _ _ x))

_>>RS_ : ∀ {Δ₁}{Δ₂}{Δ₃}{ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ERen ρ* Γ₁ Γ₂ → ESub σ* Γ₂ Γ₃ → ESub (ρ* ∘ᵣₛ σ*) Γ₁ Γ₃
_>>RS_ {Δ₃ = Δ₃}{ρ* = ρ*}{σ* = σ*}{Γ₃ = Γ₃} ρ σ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-sub-ren T ρ* σ*) (σ _ _ (ρ _ _ x))

_>>SS_ : ∀ {Δ₁}{Δ₂}{Δ₃}{σ₁* : TSub Δ₁ Δ₂} {σ₂* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ESub σ₁* Γ₁ Γ₂ → ESub σ₂* Γ₂ Γ₃ → ESub (σ₁* ∘ₛₛ σ₂*) Γ₁ Γ₃
_>>SS_ {Δ₃ = Δ₃}{σ₁* = σ₁*}{σ₂* = σ₂*}{Γ₃ = Γ₃} σ₁ σ₂ l T x
  = subst (Expr Δ₃ Γ₃) (assoc-sub-sub T  σ₁* σ₂*) (Esub _ σ₂ (σ₁ _ _ x))

_>>RR_ : ∀ {Δ₁}{Δ₂}{Δ₃}{ρ₁* : TRen Δ₁ Δ₂} {ρ₂* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → ERen ρ₁* Γ₁ Γ₂ → ERen ρ₂* Γ₂ Γ₃ → ERen (ρ₁* ∘ᵣᵣ ρ₂*) Γ₁ Γ₃
_>>RR_ {Δ₃ = Δ₃}{ρ₁* = ρ₁*}{ρ₂* = ρ₂*}{Γ₃ = Γ₃} ρ₁ ρ₂ l T x
  = subst (λ T → inn T Γ₃) (assoc-ren-ren T ρ₁* ρ₂*) (ρ₂ _ _ (ρ₁ _ _ x))

-- Fusion Lemmas ---------------------------------------------------------------

fun-ext-h-ERen :
  ∀ {σ* σ*′ : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁}{Γ₂ Γ₂′ : TEnv Δ₂}
    {σ : ERen σ* Γ₁ Γ₂} {σ′ : ERen σ*′ Γ₁ Γ₂′} →
    σ* ≡ σ*′ →
    Γ₂ ≡ Γ₂′ →
    (∀ l T x → σ l T x ≅ σ′ l T x) →
    σ ≅ σ′
fun-ext-h-ERen {Δ₁} {Δ₂} {σ*} {σ*′} {Γ₁} {Γ₂} {Γ₂′} {σ} {σ′} eq-σ eq-Γ₂ f =
  fun-ext-h (λ l → dep-ext λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → inn (Tren ■₂ T) ■₁) eq-Γ₂ eq-σ) λ l →
  fun-ext-h               (λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → inn (Tren ■₂ T) ■₁) eq-Γ₂ eq-σ) λ T →
  fun-ext-h                             (λ x → cong₂ (λ ■₁ ■₂ → inn (Tren ■₂ T) ■₁) eq-Γ₂ eq-σ) λ x →
  f l T x

fun-ext-h-ESub :
  ∀ {σ* σ*′ : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁}{Γ₂ Γ₂′ : TEnv Δ₂}
    {σ : ESub σ* Γ₁ Γ₂} {σ′ : ESub σ*′ Γ₁ Γ₂′} →
    σ* ≡ σ*′ →
    Γ₂ ≡ Γ₂′ →
    (∀ l T x → σ l T x ≅ σ′ l T x) →
    σ ≅ σ′
fun-ext-h-ESub {Δ₁} {Δ₂} {σ*} {σ*′} {Γ₁} {Γ₂} {Γ₂′} {σ} {σ′} eq-σ eq-Γ₂ f =
  fun-ext-h (λ l → dep-ext λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → Expr Δ₂ ■₁ (Tsub ■₂ T)) eq-Γ₂ eq-σ) λ l →
  fun-ext-h               (λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → Expr Δ₂ ■₁ (Tsub ■₂ T)) eq-Γ₂ eq-σ) λ T →
  fun-ext-h                             (λ x → cong₂ (λ ■₁ ■₂ → Expr Δ₂ ■₁ (Tsub ■₂ T)) eq-Γ₂ eq-σ) λ x →
  f l T x

Hcong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d} {x y u v i j}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → i ≅ j → f x u i ≅ f y v j
Hcong₃ f refl refl refl = refl

Hcong₄ : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
            {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
        {x y u v i j p q}
        (f : (x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w) → x ≅ y → u ≅ v → i ≅ j → p ≅ q → f x u i p ≅ f y v j q
Hcong₄ f refl refl refl refl = refl

-- ∘ᵣᵣ Fusion

Eren↑-dist-∘ᵣᵣ :
  ∀ {ρ* : TRen Δ₁ Δ₂}{σ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (ρ : ERen ρ* Γ₁ Γ₂) → (σ : ERen σ* Γ₂ Γ₃) →
  Eliftᵣ {T = T} ρ* ρ >>RR Eliftᵣ σ* σ ≅ Eliftᵣ {T = T} (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)
Eren↑-dist-∘ᵣᵣ {Δ₃ = Δ₃} {l = l'} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} T ρ σ =
  fun-ext-h-ERen refl (cong (_◁ Γ₃) (assoc-ren-ren T ρ* σ*)) λ l T′ → λ where
  here →
    let
      F₁ = (λ ■ → inn ■ (Tren σ* (Tren ρ* T) ◁ Γ₃)) ; E₁ = (assoc-ren-ren T ρ* σ*) ; sub₁ = subst F₁ E₁
    in
    R.begin
      sub₁ here
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      here
    R.≅⟨ H.cong {B = λ ■ → inn ■ (■ ◁ Γ₃)} (λ ■ → here) (H.≡-to-≅ (assoc-ren-ren T ρ* σ*)) ⟩ 
      here
    R.∎
  (there x) →
    let
      F₁ = (λ ■ → inn ■ (Tren σ* (Tren ρ* T) ◁ Γ₃)) ; E₁ = (assoc-ren-ren T′ ρ* σ*) ; sub₁ = subst F₁ E₁
      F₈ = (λ ■ → inn ■ Γ₃)                         ; E₈ = E₁                       ; sub₈ = subst F₈ E₈
    in
    R.begin
      (Eliftᵣ {T = T} ρ* ρ >>RR Eliftᵣ σ* σ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (there (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      there (σ l (Tren ρ* T′) (ρ l T′ x))
    R.≅⟨ Hcong₃ {C = λ ■ _ → inn ■ Γ₃} (λ ■₁ ■₂ ■₃ → there {T = ■₁} {T′ = ■₂} ■₃ )
                (H.≡-to-≅ E₈)
                (H.≡-to-≅ (assoc-ren-ren T ρ* σ*))
                (H.sym (H.≡-subst-removable F₈ E₈ _))
                ⟩
      there (sub₈ (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ refl ⟩
      Eliftᵣ {T = T} (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) l T′ (there x)
    R.∎

Eren↑-dist-∘ᵣᵣ-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃) →
  Eliftᵣ-l {l = l} ρ* ρ >>RR Eliftᵣ-l σ* σ ≅ Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)
Eren↑-dist-∘ᵣᵣ-l {Δ₁} {Δ₂} {Δ₃} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l} ρ σ =
  fun-ext-h-ERen (sym (ren↑-dist-∘ᵣᵣ l ρ* σ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₂ = (λ ■ → inn ■ (l ◁* Γ₃)) ; E₂ = (assoc-ren-ren T (Tliftᵣ ρ* l) (Tliftᵣ σ* l)) ; sub₂ = subst F₂ E₂
        F₃ = id ; E₃ = (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _))) ; sub₃ = subst F₃ E₃
        F₄ = id ; E₄ = (cong (λ T → inn T (l ◁* Γ₃)) (sym (swap-Tren-Twk σ* _))) ; sub₄ = subst F₄ E₄
        F₅ = id ; E₅ = (cong (λ T → inn T (l ◁* Γ₃)) (sym (swap-Tren-Twk (ρ* ∘ᵣᵣ σ*) _))); sub₅ = subst F₅ E₅
        F₆ = (λ T → inn T Γ₃) ; E₆ = (assoc-ren-ren T′ ρ* σ*) ; sub₆ = subst F₆ E₆
      in
      R.begin
        (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) l′ T (tskip x)
      R.≅⟨ refl ⟩
        sub₂ (Eliftᵣ-l σ* σ _ _ (Eliftᵣ-l ρ* ρ _ _ (tskip x)))
      R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
        Eliftᵣ-l σ* σ _ _ (Eliftᵣ-l ρ* ρ _ _ (tskip x))
      R.≅⟨ refl ⟩
        Eliftᵣ-l σ* σ _ _ (sub₃ (tskip (ρ _ _ x)))
      R.≅⟨ H.cong₂ {B = λ ■ → inn ■ (l ◁* Γ₂)} (λ _ → Eliftᵣ-l σ* σ _ _) (H.≡-to-≅ (swap-Tren-Twk ρ* T′)) (H.≡-subst-removable F₃ E₃ _) ⟩
        Eliftᵣ-l σ* σ _ _ (tskip (ρ _ _ x))
      R.≅⟨ refl ⟩
        sub₄ (tskip (σ _ _ (ρ _ _ x)))
      R.≅⟨ H.≡-subst-removable F₄ E₄ _ ⟩
        tskip (σ _ _ (ρ _ _ x))
      R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₃} (λ _ → tskip) (H.≡-to-≅ (assoc-ren-ren T′ ρ* σ*)) (H.sym (H.≡-subst-removable F₆ E₆ _)) ⟩
        tskip (sub₆ (σ _ _ (ρ _ _ x)))
      R.≅⟨ refl ⟩
        tskip ((ρ >>RR σ) l′ T′ x)
      R.≅⟨ H.sym (H.≡-subst-removable F₅ E₅ _) ⟩
        sub₅ (tskip ((ρ >>RR σ) l′ T′ x))
      R.≅⟨ refl ⟩
        Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) l′ T (tskip x)
      R.∎

mutual
  Eassoc-ren↑-ren↑-l :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃) →
    Eren (Tliftᵣ ρ* l′ ∘ᵣᵣ Tliftᵣ σ* l′) (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) e ≅
    Eren (Tliftᵣ (ρ* ∘ᵣᵣ σ*) l′) (Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
  Eassoc-ren↑-ren↑-l {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e ρ σ =
    R.begin
      Eren (Tliftᵣ ρ* l′ ∘ᵣᵣ Tliftᵣ σ* l′) (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Eren {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (ren↑-dist-∘ᵣᵣ l′ ρ* σ*))) (Eren↑-dist-∘ᵣᵣ-l ρ σ) ⟩
      Eren (Tliftᵣ (ρ* ∘ᵣᵣ σ*) l′) (Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
    R.∎

  Eassoc-ren↑-ren↑ :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃) →
    Eren σ* (Eliftᵣ {T = Tren ρ* T′} σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e) ≅
    Eren (ρ* ∘ᵣᵣ σ*) (Eliftᵣ {T = T′} (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
  Eassoc-ren↑-ren↑ {Δ₃ = Δ₃} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e ρ σ =
    R.begin
      Eren σ* (Eliftᵣ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Eassoc-ren-ren' e (Eliftᵣ ρ* ρ) (Eliftᵣ σ* σ) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) ((Eliftᵣ ρ* ρ) >>RR (Eliftᵣ σ* σ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ERen (ρ* ∘ᵣᵣ σ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Eren (ρ* ∘ᵣᵣ σ*) ■ e)
                 (H.≡-to-≅ (assoc-ren-ren T′ ρ* σ*)) (Eren↑-dist-∘ᵣᵣ _ ρ σ) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (Eliftᵣ (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
    R.∎

  Eassoc-ren-ren' : 
      {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃)
    → Eren σ* σ (Eren ρ* ρ e) ≅ Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) ρ σ =
    refl
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) ρ σ =
    let F₁ = (λ ■ → inn ■ Γ₃) ; E₁ = (assoc-ren-ren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Eren σ* σ (Eren ρ* ρ (` x))
    R.≅⟨ refl ⟩
      ` σ l (Tren ρ* T) (ρ l T x)
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₃} {C = λ ■ _ → Expr Δ₃ Γ₃ ■} (λ ■ → `_ {Γ = Γ₃} {T = ■})
                 (H.≡-to-≅ (assoc-ren-ren T ρ* σ*)) (H.sym (H.≡-subst-removable F₁ E₁ _)) ⟩
      ` sub₁ (σ l (Tren ρ* T) (ρ l T x))
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (` x)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) ρ σ =
    R.begin
      ƛ Eren σ* (Eliftᵣ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (assoc-ren-ren T₁ ρ* σ*))
                (H.≡-to-≅ (assoc-ren-ren T₂ ρ* σ*))
                (Eassoc-ren↑-ren↑ e ρ σ)  ⟩
      ƛ (Eren (ρ* ∘ᵣᵣ σ*) (Eliftᵣ (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e)
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (ƛ e)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) ρ σ =
    R.begin
      Eren σ* σ (Eren ρ* ρ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Eren σ* σ (Eren ρ* ρ e₁) · Eren σ* σ (Eren ρ* ρ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (assoc-ren-ren T ρ* σ*)) (H.≡-to-≅ (assoc-ren-ren T₁ ρ* σ*))
                (Eassoc-ren-ren' e₁ ρ σ) (Eassoc-ren-ren' e₂ ρ σ) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e₁ · Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e₂
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (e₁ · e₂)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) ρ σ =
    R.begin
      Eren σ* σ (Eren ρ* ρ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Eren (Tliftᵣ σ* l) (Eliftᵣ-l σ* σ) (Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (assoc-ren-ren T (Tliftᵣ ρ* _) (Tliftᵣ σ* _)))
                 (Eassoc-ren-ren' e (Eliftᵣ-l ρ* ρ) (Eliftᵣ-l σ* σ)) ⟩
      Λ l ⇒ Eren (Tliftᵣ ρ* l ∘ᵣᵣ Tliftᵣ σ* l) (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tren σ T) (sym (ren↑-dist-∘ᵣᵣ _ ρ* σ*))))
                 (Eassoc-ren↑-ren↑-l e ρ σ) ⟩
      Λ l ⇒ Eren (Tliftᵣ (ρ* ∘ᵣᵣ σ*) l) (Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (Λ l ⇒ e)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) ρ σ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tren-[] ρ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tren-[] (ρ* ∘ᵣᵣ σ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tren-[] σ* (Tren (Tliftᵣ ρ* _) T) (Tren ρ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Eren σ* σ (Eren ρ* ρ (e ∙ T′))
    R.≅⟨ refl ⟩
      Eren σ* σ (sub₂ (Eren ρ* ρ e ∙ Tren ρ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Eren σ* σ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Eren σ* σ (Eren ρ* ρ e ∙ Tren ρ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Eren σ* σ (Eren ρ* ρ e) ∙ Tren σ* (Tren ρ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Eren σ* σ (Eren ρ* ρ e) ∙ Tren σ* (Tren ρ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-ren↑-ren↑ T ρ* σ*)) (Eassoc-ren-ren' e ρ σ) (H.≡-to-≅ (assoc-ren-ren T′ ρ* σ*)) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e ∙ Tren (ρ* ∘ᵣᵣ σ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e ∙ (Tren (ρ* ∘ᵣᵣ σ*) T′))
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (e ∙ T′)
    R.∎ 

-- ∘ᵣₛ Fusion

Esub↑-dist-∘ᵣₛ :
  ∀ {ρ* : TRen Δ₁ Δ₂}{σ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (ρ : ERen ρ* Γ₁ Γ₂) → (σ : ESub σ* Γ₂ Γ₃) →
  Eliftᵣ {T = T} ρ* ρ >>RS Eliftₛ σ* σ ≅ Eliftₛ {T = T} (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)
Esub↑-dist-∘ᵣₛ {Δ₃ = Δ₃} {l = l'} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} T ρ σ =
  fun-ext-h-ESub refl (cong (_◁ Γ₃) (assoc-sub-ren T ρ* σ*)) λ l T′ → λ where
  here →
    let
      F₁ = (Expr _ (Tsub σ* (Tren ρ* T) ◁ Γ₃))          ; E₁ = (assoc-sub-ren T ρ* σ*)            ; sub₁ = subst F₁ E₁
      F₃ = (Expr _ Γ₃)                                  ; E₃ = λ l₂ T₂ → (assoc-sub-ren T₂ ρ* σ*) ; sub₃ = λ l₂ T₂ → subst F₃ (E₃ l₂ T₂)
    in
    R.begin
      sub₁ (` here)
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      ` here
    R.≅⟨ H.cong {B = λ ■ → Expr _ (■ ◁ Γ₃) ■} (λ ■ → `_ {Γ = ■ ◁ Γ₃} {T = ■} here) (H.≡-to-≅ (assoc-sub-ren T ρ* σ*)) ⟩ 
      ` here
    R.≅⟨ refl ⟩
      Eliftₛ (ρ* ∘ᵣₛ σ*) (λ l₂ T₂ x → sub₃ l₂ T₂ (σ l₂ (Tren ρ* T₂) (ρ l₂ T₂ x))) _ T here
    R.∎
  (there x) →
    let
      F₁ = (Expr _ (Tsub σ* (Tren ρ* T) ◁ Γ₃))              ; E₁ = (assoc-sub-ren T′ ρ* σ*)                      ; sub₁ = subst F₁ E₁
      F₂ = (Expr _ (Tsub σ* (Tren ρ* T) ◁ Γ₃))              ; E₂ = (TidᵣT≡T (Tsub σ* (Tren ρ* T′)))              ; sub₂ = subst F₂ E₂
      F₇ = (Expr _ (Tsub (λ z x₁ → σ* z (ρ* z x₁)) T ◁ Γ₃)) ; E₇ = (TidᵣT≡T (Tsub (λ z x₁ → σ* z (ρ* z x₁)) T′)) ; sub₇ = subst F₇ E₇
      F₈ = (Expr _ Γ₃)                                      ; E₈ = E₁                                            ; sub₈ = subst F₈ E₈
    in
    R.begin
      (Eliftᵣ {T = T} ρ* ρ >>RS Eliftₛ σ* σ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (Eren Tidᵣ
        (λ l₁ T₂ x₁ → there (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (Eren Tidᵣ
        (λ l₁ T₂ x₁ → there (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      Eren {Γ₂ = Tsub σ* (Tren ρ* T) ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))
    R.≅⟨ H.cong (λ ■ → Eren {Γ₂ = ■ ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))) (H.≡-to-≅ (assoc-sub-ren T ρ* σ*)) ⟩
      Eren {Γ₂ = Tsub (ρ* ∘ᵣₛ σ*) T ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))
    R.≅⟨ H.cong₂ {B = λ ■ → Expr Δ₃ Γ₃ ■}
                  (λ _ ■ → Eren Tidᵣ (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁)) ■)
                  (H.≡-to-≅ E₈)
                  (H.sym (H.≡-subst-removable F₈ E₈ _)) ⟩
      Eren {Γ₂ = Tsub (ρ* ∘ᵣₛ σ*) T ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (sub₈ (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ H.sym (H.≡-subst-removable F₇ E₇ _) ⟩
      sub₇ (Eren Tidᵣ
        (λ l₁ T₂ x₁ → there (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (sub₈ (σ l (Tren ρ* T′) (ρ l T′ x))))
    R.≅⟨ refl ⟩
      Ewk ((ρ >>RS σ) _ _ x)
    R.≅⟨ refl ⟩
      Eliftₛ {T = T} (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) l T′ (there x)
    R.∎

Esub↑-dist-∘ᵣₛ-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃) →
  Eliftᵣ-l {l = l} ρ* ρ >>RS Eliftₛ-l σ* σ ≅ Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)
Esub↑-dist-∘ᵣₛ-l {Δ₁} {Δ₂} {Δ₃} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l} ρ σ =
  fun-ext-h-ESub (sym (sub↑-dist-∘ᵣₛ l ρ* σ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₂ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₂ = (assoc-sub-ren T (Tliftᵣ ρ* l) (Tliftₛ σ* l))
                                       ; sub₂ = subst F₂ E₂
        F₃ = (λ x → x) ; E₃ = (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _)))
                       ; sub₃ = subst F₃ E₃
        F₅ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₅ = sym (swap-Tsub-Twk (ρ* ∘ᵣₛ σ*) T′) ; sub₅ = subst F₅ E₅
        F₇ = (Expr _ _) ; E₇ = (sym (swap-Tsub-Twk σ* (Tren ρ* T′))) ; sub₇ = subst F₇ E₇
        F₈ = (Expr Δ₃ Γ₃) ; E₈ = (assoc-sub-ren T′ ρ* σ*) ; sub₈ = subst F₈ E₈
      in
      R.begin
        (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) l′ T (tskip x)
      R.≅⟨ refl ⟩
        sub₂ (Eliftₛ-l σ* σ _ _ (Eliftᵣ-l ρ* ρ _ _ (tskip x)))
      R.≅⟨ refl ⟩
        sub₂ (Eliftₛ-l σ* σ _ _ (sub₃ (tskip {T = Tren ρ* T′} (ρ _ _ x))))
      R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
        Eliftₛ-l σ* σ l′ (Tren (Tliftᵣ ρ* l) (Twk T′)) (sub₃ (tskip {T = Tren ρ* T′} (ρ _ _ x)))
      R.≅⟨ H.cong₂ (Eliftₛ-l σ* σ l′) (H.≡-to-≅ (swap-Tren-Twk ρ* _)) (H.≡-subst-removable F₃ E₃ _) ⟩
        Eliftₛ-l σ* σ l′ (Twk (Tren ρ* T′)) (tskip {T = Tren ρ* T′} (ρ _ _ x))
      R.≅⟨ refl ⟩
        sub₇ (Ewk-l (σ _ _ (ρ _ _ x)))
      R.≅⟨ H.≡-subst-removable F₇ E₇ _ ⟩
        Ewk-l {T = Tsub σ* (Tren ρ* T′)} (σ _ _ (ρ _ _ x))
      R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ ■₁ ■₂ → Ewk-l ■₂) (H.≡-to-≅ E₈) (H.sym (H.≡-subst-removable F₈ E₈ _)) ⟩
        Ewk-l {T = Tsub (ρ* ∘ᵣₛ σ*) T′} (sub₈ (σ _ _ (ρ _ _ x)))
      R.≅⟨ refl ⟩
        Ewk-l ((ρ >>RS σ) l′ T′ x)
      R.≅⟨ H.sym (H.≡-subst-removable F₅ E₅ _) ⟩
        sub₅ (Ewk-l ((ρ >>RS σ) l′ T′ x))
      R.≅⟨ refl ⟩
        Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) l′ T (tskip x)
      R.∎

mutual
  Eassoc-sub↑-ren↑-l :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃) →
    Esub (Tliftᵣ ρ* l′ ∘ᵣₛ Tliftₛ σ* l′) (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) e ≅
    Esub (Tliftₛ (ρ* ∘ᵣₛ σ*) l′) (Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
  Eassoc-sub↑-ren↑-l {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e ρ σ =
    R.begin
      Esub (Tliftᵣ ρ* l′ ∘ᵣₛ Tliftₛ σ* l′) (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Esub {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (sub↑-dist-∘ᵣₛ l′ ρ* σ*))) (Esub↑-dist-∘ᵣₛ-l ρ σ) ⟩
      Esub (Tliftₛ (ρ* ∘ᵣₛ σ*) l′) (Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
    R.∎

  Eassoc-sub↑-ren↑ :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃) →
    Esub σ* (Eliftₛ {T = Tren ρ* T′} σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e) ≅
    Esub (ρ* ∘ᵣₛ σ*) (Eliftₛ {T = T′} (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
  Eassoc-sub↑-ren↑ {Δ₃ = Δ₃} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e ρ σ =
    R.begin
      Esub σ* (Eliftₛ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Eassoc-sub-ren' e (Eliftᵣ ρ* ρ) (Eliftₛ σ* σ) ⟩
      Esub (ρ* ∘ᵣₛ σ*) ((Eliftᵣ ρ* ρ) >>RS (Eliftₛ σ* σ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ESub (ρ* ∘ᵣₛ σ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Esub (ρ* ∘ᵣₛ σ*) ■ e)
                 (H.≡-to-≅ (assoc-sub-ren T′ ρ* σ*)) (Esub↑-dist-∘ᵣₛ _ ρ σ) ⟩
      Esub (ρ* ∘ᵣₛ σ*) (Eliftₛ (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
    R.∎

  Eassoc-sub-ren' : 
      {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃)
    → Esub σ* σ (Eren ρ* ρ e) ≅ Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e
  Eassoc-sub-ren' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) ρ σ =
    refl
  Eassoc-sub-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) ρ σ =
    let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-sub-ren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Esub σ* σ (Eren ρ* ρ (` x))
    R.≅⟨ refl ⟩
      σ l (Tren ρ* T) (ρ l T x)
    R.≅⟨ H.sym (H.≡-subst-removable F₁ E₁ _) ⟩
      sub₁ (σ l (Tren ρ* T) (ρ l T x))
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (` x)
    R.∎
  Eassoc-sub-ren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) ρ σ =
    R.begin
      ƛ Esub σ* (Eliftₛ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (assoc-sub-ren T₁ ρ* σ*))
                (H.≡-to-≅ (assoc-sub-ren T₂ ρ* σ*))
                (Eassoc-sub↑-ren↑ e ρ σ)  ⟩
      ƛ (Esub (ρ* ∘ᵣₛ σ*) (Eliftₛ (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e)
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (ƛ e)
    R.∎
  Eassoc-sub-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) ρ σ =
    R.begin
      Esub σ* σ (Eren ρ* ρ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Esub σ* σ (Eren ρ* ρ e₁) · Esub σ* σ (Eren ρ* ρ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (assoc-sub-ren T ρ* σ*)) (H.≡-to-≅ (assoc-sub-ren T₁ ρ* σ*))
                (Eassoc-sub-ren' e₁ ρ σ) (Eassoc-sub-ren' e₂ ρ σ) ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e₁ · Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e₂
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (e₁ · e₂)
    R.∎
  Eassoc-sub-ren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) ρ σ =
    R.begin
      Esub σ* σ (Eren ρ* ρ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) (Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (assoc-sub-ren T (Tliftᵣ ρ* _) (Tliftₛ σ* _)))
                 (Eassoc-sub-ren' e (Eliftᵣ-l ρ* ρ) (Eliftₛ-l σ* σ)) ⟩
      Λ l ⇒ Esub (Tliftᵣ ρ* l ∘ᵣₛ Tliftₛ σ* l) (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ᵣₛ _ ρ* σ*))))
                 (Eassoc-sub↑-ren↑-l e ρ σ) ⟩
      Λ l ⇒ Esub (Tliftₛ (ρ* ∘ᵣₛ σ*) l) (Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (Λ l ⇒ e)
    R.∎
  Eassoc-sub-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) ρ σ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tren-[] ρ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tsub-[] (ρ* ∘ᵣₛ σ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tsub-[] σ* (Tren (Tliftᵣ ρ* _) T) (Tren ρ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Esub σ* σ (Eren ρ* ρ (e ∙ T′))
    R.≅⟨ refl ⟩
      Esub σ* σ (sub₂ (Eren ρ* ρ e ∙ Tren ρ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Esub σ* σ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Esub σ* σ (Eren ρ* ρ e ∙ Tren ρ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Esub σ* σ (Eren ρ* ρ e) ∙ Tsub σ* (Tren ρ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Esub σ* σ (Eren ρ* ρ e) ∙ Tsub σ* (Tren ρ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-sub↑-ren↑ T ρ* σ*)) (Eassoc-sub-ren' e ρ σ) (H.≡-to-≅ (assoc-sub-ren T′ ρ* σ*)) ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e ∙ Tsub (ρ* ∘ᵣₛ σ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e ∙ (Tsub (ρ* ∘ᵣₛ σ*) T′))
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (e ∙ T′)
    R.∎ 

-- Swap-Lemmas for Renamings

swap-ren-Ewk :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ERen ρ* Γ₁ Γ₂) (T : Type Δ₁ l) →
  Ewkᵣ {T = T} Tidᵣ Eidᵣ >>RR Eliftᵣ ρ* ρ ≅
  ρ >>RR Ewkᵣ {T = Tren ρ* T} Tidᵣ Eidᵣ
swap-ren-Ewk {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} ρ T =
  fun-ext-h-ERen refl refl λ l₁ T₁ x →
    let
      F₁ = (λ T₂ → inn T₂ (Tren ρ* T ◁ Γ₂)) ; E₁ = (assoc-ren-ren T₁ Tidᵣ ρ*)   ; sub₁ = subst F₁ E₁
      F₂ = (λ T₂ → inn T₂ Γ₁)               ; E₂ = (sym (TidᵣT≡T T₁))           ; sub₂ = subst F₂ E₂
      F₃ = (λ T₂ → inn T₂ (Tren ρ* T ◁ Γ₂)) ; E₃ = (assoc-ren-ren T₁ ρ* Tidᵣ)   ; sub₃ = subst F₃ E₃
      F₄ = (λ T₂ → inn T₂ Γ₂)               ; E₄ = (sym (TidᵣT≡T (Tren ρ* T₁))) ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Ewkᵣ Tidᵣ Eidᵣ >>RR Eliftᵣ ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (there (ρ l₁ (Tren Tidᵣ T₁) (sub₂ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      there (ρ l₁ (Tren Tidᵣ T₁) (sub₂ x))
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₁} (λ ■₁ ■₂ → inn.there (ρ l₁ ■₁ ■₂))
                 (H.≡-to-≅ (TidᵣT≡T T₁)) (H.≡-subst-removable F₂ E₂ _) ⟩
      there (ρ l₁ T₁ x)
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₂} (λ _ → inn.there)
                 (H.≡-to-≅ (sym (TidᵣT≡T (Tren ρ* T₁)))) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
      there (sub₄ (ρ l₁ T₁ x))
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (there (sub₄ (ρ l₁ T₁ x)))
    R.≅⟨ refl ⟩
      (ρ >>RR Ewkᵣ Tidᵣ Eidᵣ) l₁ T₁ x
    R.∎

swap-Eren-Ewk :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ERen ρ* Γ₁ Γ₂) (T′ : Type Δ₁ l′) (e : Expr Δ₁ Γ₁ T) →
  Eren ρ* (Eliftᵣ {T = T′} ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e) ≅
  Eren Tidᵣ (Ewkᵣ {T = Tren ρ* T′} Tidᵣ Eidᵣ) (Eren ρ* ρ e)
swap-Eren-Ewk {Δ₁} {Δ₂} {l} {l′} {ρ*} {Γ₁} {Γ₂} {T} ρ T′ e =
  R.begin
    Eren ρ* (Eliftᵣ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e)
  R.≅⟨ Eassoc-ren-ren' e (Ewkᵣ Tidᵣ Eidᵣ) (Eliftᵣ ρ* ρ) ⟩
    Eren ρ* (Ewkᵣ {T = T′} Tidᵣ Eidᵣ >>RR Eliftᵣ ρ* ρ) e
  R.≅⟨ H.cong (λ ■ → Eren ρ* ■ e) (swap-ren-Ewk ρ T′) ⟩
    Eren ρ* (ρ >>RR Ewkᵣ {T = Tren ρ* T′} Tidᵣ Eidᵣ) e
  R.≅⟨ H.sym (Eassoc-ren-ren' e ρ (Ewkᵣ Tidᵣ Eidᵣ)) ⟩
    Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (Eren ρ* ρ e)
  R.∎

swap-ren-Ewk-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ERen ρ* Γ₁ Γ₂) (l : Level) →
  Ewkᵣ-l l >>RR Eliftᵣ-l ρ* ρ ≅ ρ >>RR Ewkᵣ-l l
swap-ren-Ewk-l {Δ₁} {Δ₂} {ρ*} {Γ₁} {Γ₂} ρ l =
  fun-ext-h-ERen refl refl λ l₁ T₁ x →
    let
      F₁ = (λ T → inn T (l ◁* Γ₂)) ; E₁ = (assoc-ren-ren T₁ (Twkᵣ Tidᵣ) (Tliftᵣ ρ* l))              ; sub₁ = subst F₁ E₁
      F₂ = id                      ; E₂ = (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _))) ; sub₂ = subst F₂ E₂
      F₃ = (λ T → inn T (l ◁* Γ₂)) ; E₃ = (assoc-ren-ren T₁ ρ* (Twkᵣ Tidᵣ))                         ; sub₃ = subst F₃ E₃
    in
    R.begin
      (Ewkᵣ-l l >>RR Eliftᵣ-l ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (tskip (ρ l₁ T₁ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (tskip (ρ l₁ T₁ x))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      tskip (ρ l₁ T₁ x)
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (tskip (ρ l₁ T₁ x))
    R.≅⟨ refl ⟩
      (ρ >>RR Ewkᵣ-l l) l₁ T₁ x
    R.∎

swap-Eren-Ewk-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ERen ρ* Γ₁ Γ₂) (l′ : Level) (e : Expr Δ₁ Γ₁ T) →
  Eren (Tliftᵣ ρ* l′) (Eliftᵣ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e) ≅
  Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Eren ρ* ρ e)
swap-Eren-Ewk-l {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} {T} ρ l′ e =
  R.begin
    Eren (Tliftᵣ ρ* l′) (Eliftᵣ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e)
  R.≅⟨ Eassoc-ren-ren' e (Ewkᵣ-l l′) (Eliftᵣ-l ρ* ρ) ⟩
    Eren (Twkᵣ ρ*) (Ewkᵣ-l l′ >>RR Eliftᵣ-l ρ* ρ) e
  R.≅⟨ H.cong (λ ■ → Eren (Twkᵣ ρ*) ■ e) (swap-ren-Ewk-l ρ l′) ⟩
    Eren (Twkᵣ ρ*) (ρ >>RR Ewkᵣ-l l′) e
  R.≅⟨ H.sym (Eassoc-ren-ren' e ρ (Ewkᵣ-l l′)) ⟩
    Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Eren ρ* ρ e)
  R.∎

-- ∘ₛᵣ Fusion

Esub↑-dist-∘ₛᵣ :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
  Eliftₛ {T = T} σ* σ >>SR Eliftᵣ ρ* ρ ≅ Eliftₛ {T = T} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)
Esub↑-dist-∘ₛᵣ {Δ₂ = Δ₂} {Δ₃ = Δ₃} {l = l'} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} T σ ρ =
  fun-ext-h-ESub refl (cong (_◁ Γ₃) (assoc-ren-sub T σ* ρ*)) λ l T′ → λ where
  here →
    let
      F₁ = (Expr _ (Tren ρ* (Tsub σ* T) ◁ Γ₃)) ; E₁ = (assoc-ren-sub T σ* ρ*) ; sub₁ = subst F₁ E₁
    in
    R.begin
      sub₁ (` here)
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      ` here
    R.≅⟨ H.cong {B = λ ■ → Expr _ (■ ◁ Γ₃) ■} (λ ■ → `_ {Γ = ■ ◁ Γ₃} {T = ■} here) (H.≡-to-≅ (assoc-ren-sub T σ* ρ*)) ⟩ 
      ` here
    R.≅⟨ refl ⟩
      Eliftₛ (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) l' T here
    R.∎
  (there x) →
    let
      F₁ = (Expr _ (Tren ρ* (Tsub σ* T) ◁ Γ₃))                  ; E₁ = (assoc-ren-sub T′ σ* ρ*)                         ; sub₁ = subst F₁ E₁
      F₂ = (Expr _ (Tsub σ* T ◁ _))                             ; E₂ = (TidᵣT≡T (Tsub σ* T′))                           ; sub₂ = subst F₂ E₂
      F₃ = (Expr Δ₃ (Tsub (λ z x₁ → Tren ρ* (σ* z x₁)) T ◁ Γ₃)) ; E₃ = (TidᵣT≡T (Tsub (λ z x₁ → Tren ρ* (σ* z x₁)) T′)) ; sub₃ = subst F₃ E₃
      F₄ = (Expr Δ₃ Γ₃)                                         ; E₄ = E₁                                               ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Eliftₛ {T = T} σ* σ >>SR Eliftᵣ ρ* ρ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (Eren ρ* (Eliftᵣ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Eren ρ* (Eliftᵣ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x)))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ (Tsub σ* T ◁ Γ₂)} (λ _ → Eren ρ* (Eliftᵣ ρ* ρ))
                 (H.≡-to-≅ (sym (TidᵣT≡T (Tsub σ* T′)))) (H.≡-subst-removable F₂ E₂ _) ⟩
      Eren ρ* (Eliftᵣ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))
    R.≅⟨ swap-Eren-Ewk ρ (Tsub σ* T) (σ l T′ x) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tren ρ* (Tsub σ* T)} Tidᵣ Eidᵣ) (Eren ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong (λ ■ → Eren Tidᵣ (Ewkᵣ {T = ■} Tidᵣ Eidᵣ) (Eren ρ* ρ (σ l T′ x)))
                (H.≡-to-≅ (assoc-ren-sub T σ* ρ*)) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub (σ* ∘ₛᵣ ρ*) T} Tidᵣ Eidᵣ) (Eren ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ))
                 (H.≡-to-≅ (assoc-ren-sub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
      Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Eren ρ* ρ (σ l T′ x)))
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Eren ρ* ρ (σ l T′ x))))
    R.≅⟨ refl ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) ((σ >>SR ρ) _ _ x))
    R.≅⟨ refl ⟩
      Ewk ((σ >>SR ρ) _ _ x)
    R.≅⟨ refl ⟩
      Eliftₛ {T = T} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) l T′ (there x)
    R.∎

Esub↑-dist-∘ₛᵣ-l :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
  Eliftₛ-l {l = l} σ* σ >>SR Eliftᵣ-l ρ* ρ ≅ Eliftₛ-l {l = l} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)
Esub↑-dist-∘ₛᵣ-l {Δ₁} {Δ₂} {Δ₃} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l} σ ρ =
  fun-ext-h-ESub (sym (ren↑-dist-∘ₛᵣ l σ* ρ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₁ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₁ = (assoc-ren-sub (Tren (Twkᵣ Tidᵣ) T′) (Tliftₛ σ* l) (Tliftᵣ ρ* l)) ; sub₁ = subst F₁ E₁
        F₂ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₂ = (sym (swap-Tsub-Twk σ* T′))                                       ; sub₂ = subst F₂ E₂
        F₃ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₃ = (sym (swap-Tsub-Twk (σ* ∘ₛᵣ ρ*) T′))                              ; sub₃ = subst F₃ E₃
        F₄ = (Expr Δ₃ Γ₃)              ; E₄ = (assoc-ren-sub T′ σ* ρ*)                                          ; sub₄ = subst F₄ E₄
      in
      R.begin
        (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) l′ (Twk T′) (tskip x)
      R.≅⟨ refl ⟩
        sub₁ (Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))))
      R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
        Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x)))
      R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₂) (l ◁* Γ₂)} (λ _ → Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ))
                   (H.≡-to-≅ (swap-Tsub-Twk σ* T′)) (H.≡-subst-removable F₂ E₂ _) ⟩
        Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))
      R.≅⟨ swap-Eren-Ewk-l ρ l (σ l′ T′ x) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (Eren ρ* ρ (σ l′ T′ x))
      R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l))
                   (H.≡-to-≅ (assoc-ren-sub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Eren ρ* ρ (σ l′ T′ x)))
      R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
        sub₃ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Eren ρ* ρ (σ l′ T′ x))))
      R.≅⟨ refl ⟩
        Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) l′ (Twk T′) (tskip x)
      R.∎

mutual
  Eassoc-ren↑-sub↑-l :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
    Esub (Tliftₛ σ* l′ ∘ₛᵣ Tliftᵣ ρ* l′) (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) e ≅
    Esub (Tliftₛ (σ* ∘ₛᵣ ρ*) l′) (Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
  Eassoc-ren↑-sub↑-l {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e σ ρ =
    R.begin
      Esub (Tliftₛ σ* l′ ∘ₛᵣ Tliftᵣ ρ* l′) (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Esub {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (ren↑-dist-∘ₛᵣ l′ σ* ρ*))) (Esub↑-dist-∘ₛᵣ-l σ ρ) ⟩
      Esub (Tliftₛ (σ* ∘ₛᵣ ρ*) l′) (Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
    R.∎

  Eassoc-ren↑-sub↑ :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
    Eren ρ* (Eliftᵣ {T = Tsub σ* T′} ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e) ≅
    Esub (σ* ∘ₛᵣ ρ*) (Eliftₛ {T = T′} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
  Eassoc-ren↑-sub↑ {Δ₃ = Δ₃} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e σ ρ =
    R.begin
      Eren ρ* (Eliftᵣ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ Eassoc-ren-sub' e (Eliftₛ σ* σ) (Eliftᵣ ρ* ρ) ⟩
      Esub (σ* ∘ₛᵣ ρ*) ((Eliftₛ σ* σ) >>SR (Eliftᵣ ρ* ρ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ESub (σ* ∘ₛᵣ ρ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Esub (σ* ∘ₛᵣ ρ*) ■ e)
                 (H.≡-to-≅ (assoc-ren-sub T′ σ* ρ*)) (Esub↑-dist-∘ₛᵣ _ σ ρ) ⟩
      Esub (σ* ∘ₛᵣ ρ*) (Eliftₛ (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
    R.∎

  Eassoc-ren-sub' : 
      {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃)
    → Eren ρ* ρ (Esub σ* σ e) ≅ Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e
  Eassoc-ren-sub' {Δ₁} {Δ₂} {Δ₃} {.zero} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) σ ρ =
    refl
  Eassoc-ren-sub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) σ ρ =
    let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-ren-sub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Eren ρ* ρ (Esub σ* σ (` x))
    R.≅⟨ refl ⟩
      Eren ρ* ρ (σ l T x)
    R.≅⟨ H.sym (H.≡-subst-removable F₁ E₁ _) ⟩
      sub₁ (Eren ρ* ρ (σ l T x))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (` x)
    R.∎
  Eassoc-ren-sub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) σ ρ =
    R.begin
      ƛ Eren ρ* (Eliftᵣ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (assoc-ren-sub T₁ σ* ρ*))
                (H.≡-to-≅ (assoc-ren-sub T₂ σ* ρ*))
                (Eassoc-ren↑-sub↑ e σ ρ)  ⟩
      ƛ (Esub (σ* ∘ₛᵣ ρ*) (Eliftₛ (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e)
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (ƛ e)
    R.∎
  Eassoc-ren-sub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) σ ρ =
    R.begin
      Eren ρ* ρ (Esub σ* σ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Eren ρ* ρ (Esub σ* σ e₁) · Eren ρ* ρ (Esub σ* σ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (assoc-ren-sub T σ* ρ*)) (H.≡-to-≅ (assoc-ren-sub T₁ σ* ρ*))
                (Eassoc-ren-sub' e₁ σ ρ) (Eassoc-ren-sub' e₂ σ ρ) ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e₁ · Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e₂
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (e₁ · e₂)
    R.∎
  Eassoc-ren-sub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) σ ρ =
    R.begin
      Eren ρ* ρ (Esub σ* σ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (assoc-ren-sub T (Tliftₛ σ* _) (Tliftᵣ ρ* _)))
                 (Eassoc-ren-sub' e (Eliftₛ-l σ* σ) (Eliftᵣ-l ρ* ρ)) ⟩
      Λ l ⇒ Esub (Tliftₛ σ* l ∘ₛᵣ Tliftᵣ ρ* l) (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tsub σ T) (sym (ren↑-dist-∘ₛᵣ _ σ* ρ*))))
                 (Eassoc-ren↑-sub↑-l e σ ρ) ⟩
      Λ l ⇒ Esub (Tliftₛ (σ* ∘ₛᵣ ρ*) l) (Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (Λ l ⇒ e)
    R.∎
  Eassoc-ren-sub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) σ ρ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tsub-[] σ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tsub-[] (σ* ∘ₛᵣ ρ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tren-[] ρ* (Tsub (Tliftₛ σ* _) T) (Tsub σ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Eren ρ* ρ (Esub σ* σ (e ∙ T′))
    R.≅⟨ refl ⟩
      Eren ρ* ρ (sub₂ (Esub σ* σ e ∙ Tsub σ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Eren ρ* ρ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Eren ρ* ρ (Esub σ* σ e ∙ Tsub σ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Eren ρ* ρ (Esub σ* σ e) ∙ Tren ρ* (Tsub σ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Eren ρ* ρ (Esub σ* σ e) ∙ Tren ρ* (Tsub σ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-ren↑-sub↑ T σ* ρ*)) (Eassoc-ren-sub' e σ ρ) (H.≡-to-≅ (assoc-ren-sub T′ σ* ρ*)) ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e ∙ Tsub (σ* ∘ₛᵣ ρ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e ∙ (Tsub (σ* ∘ₛᵣ ρ*) T′))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (e ∙ T′)
    R.∎ 

-- Swap-Lemmas for Substitutions

swap-sub-Ewk :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ESub ρ* Γ₁ Γ₂) (T : Type Δ₁ l) →
  Ewkᵣ {T = T} Tidᵣ Eidᵣ >>RS Eliftₛ ρ* ρ ≅
  ρ >>SR Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ
swap-sub-Ewk {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} ρ T =
  fun-ext-h-ESub (sym (∘ₛᵣ-neutralˡ ρ*)) refl λ l₁ T₁ x →
    let
      F₁ = (Expr Δ₂ (Tsub ρ* T ◁ Γ₂)) ; E₁ = (assoc-sub-ren T₁ Tidᵣ ρ*)                  ; sub₁ = subst F₁ E₁
      F₂ = (Expr Δ₂ (Tsub ρ* T ◁ Γ₂)) ; E₂ = (TidᵣT≡T (Tsub ρ* (Tren (λ _ x₁ → x₁) T₁))) ; sub₂ = subst F₂ E₂
      F₃ = (λ T₂ → inn T₂ Γ₁)         ; E₃ = (sym (TidᵣT≡T T₁))                          ; sub₃ = subst F₃ E₃
      F₄ = (Expr Δ₂ (Tsub ρ* T ◁ Γ₂)) ; E₄ = (assoc-ren-sub T₁ ρ* (λ _ x₁ → x₁))         ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Ewkᵣ {T = T} Tidᵣ Eidᵣ >>RS Eliftₛ ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ (Tren Tidᵣ T₁) (sub₃ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ (Tren Tidᵣ T₁) (sub₃ x)))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ (Tren Tidᵣ T₁) (sub₃ x))
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₁} (λ ■₁ ■₂ → Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ ■₁ ■₂))
                 (H.≡-to-≅ (TidᵣT≡T T₁)) (H.≡-subst-removable F₃ E₃ _) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ T₁ x)
    R.≅⟨ H.sym (H.≡-subst-removable F₄ E₄ _) ⟩
      sub₄ (Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ T₁ x))
    R.≅⟨ refl ⟩
      (ρ >>SR Ewkᵣ Tidᵣ Eidᵣ) l₁ T₁ x
    R.∎

swap-Esub-Ewk :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ESub ρ* Γ₁ Γ₂) (T′ : Type Δ₁ l′) (e : Expr Δ₁ Γ₁ T) →
  Esub ρ* (Eliftₛ {T = T′} ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e) ≅
  Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T′} Tidᵣ Eidᵣ) (Esub ρ* ρ e)
swap-Esub-Ewk {Δ₁} {Δ₂} {l} {l′} {ρ*} {Γ₁} {Γ₂} {T} ρ T′ e =
  R.begin
    Esub ρ* (Eliftₛ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e)
  R.≅⟨ Eassoc-sub-ren' e (Ewkᵣ Tidᵣ Eidᵣ) (Eliftₛ ρ* ρ) ⟩
    Esub ρ* (Ewkᵣ {T = T′} Tidᵣ Eidᵣ >>RS Eliftₛ ρ* ρ) e
  R.≅⟨ H.cong₂ {B = λ ■ → ESub ■ Γ₁ (Tsub ρ* T′ ◁ Γ₂)} (λ ■₁ ■₂ → Esub ■₁ ■₂ e)
               (H.≡-to-≅ (sym (∘ₛᵣ-neutralˡ ρ*))) (swap-sub-Ewk ρ T′) ⟩
    Esub (ρ* ∘ₛᵣ Tidᵣ) (ρ >>SR Ewkᵣ {T = Tsub ρ* T′} Tidᵣ Eidᵣ) e
  R.≅⟨ H.sym (Eassoc-ren-sub' e ρ (Ewkᵣ Tidᵣ Eidᵣ)) ⟩
    Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (Esub ρ* ρ e)
  R.∎

swap-sub-Ewk-l :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ESub ρ* Γ₁ Γ₂) (l : Level) →
  Ewkᵣ-l l >>RS Eliftₛ-l ρ* ρ ≅ ρ >>SR Ewkᵣ-l l
swap-sub-Ewk-l {Δ₁} {Δ₂} {ρ*} {Γ₁} {Γ₂} ρ l =
  fun-ext-h-ESub refl refl λ l₁ T₁ x →
    let
      F₁ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₁ = (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (Tliftₛ ρ* l))              ; sub₁ = subst F₁ E₁
      F₂ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₂ = (sym (swap-Tsub-Twk ρ* T₁)) ; sub₂ = subst F₂ E₂
      F₃ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₃ = (assoc-ren-sub T₁ ρ* (Twkᵣ Tidᵣ))                         ; sub₃ = subst F₃ E₃
    in
    R.begin
      (Ewkᵣ-l l >>RS Eliftₛ-l ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x)
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x))
    R.≅⟨ refl ⟩
      (ρ >>SR Ewkᵣ-l l) l₁ T₁ x
    R.∎

swap-Esub-Ewk-l :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ESub ρ* Γ₁ Γ₂) (l′ : Level) (e : Expr Δ₁ Γ₁ T) →
  Esub (Tliftₛ ρ* l′) (Eliftₛ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e) ≅
  Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Esub ρ* ρ e)
swap-Esub-Ewk-l {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} {T} ρ l′ e =
  R.begin
    Esub (Tliftₛ ρ* l′) (Eliftₛ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e)
  R.≅⟨ Eassoc-sub-ren' e (Ewkᵣ-l l′) (Eliftₛ-l ρ* ρ) ⟩
    Esub (Twkᵣ Tidᵣ ∘ᵣₛ Tliftₛ ρ* l′) (Ewkᵣ-l l′ >>RS Eliftₛ-l ρ* ρ) e
  R.≅⟨ H.cong (λ ■ → Esub (Twkᵣ Tidᵣ ∘ᵣₛ Tliftₛ ρ* l′) ■ e) (swap-sub-Ewk-l ρ l′) ⟩
    Esub (ρ* ∘ₛᵣ Twkᵣ Tidᵣ) (ρ >>SR Ewkᵣ-l l′) e
  R.≅⟨ H.sym (Eassoc-ren-sub' e ρ (Ewkᵣ-l l′)) ⟩
    Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Esub ρ* ρ e)
  R.∎

-- ∘ₛₛ Fusion

Esub↑-dist-∘ₛₛ :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
  Eliftₛ {T = T} σ* σ >>SS Eliftₛ ρ* ρ ≅ Eliftₛ {T = T} (σ* ∘ₛₛ ρ*) (σ >>SS ρ)
Esub↑-dist-∘ₛₛ {Δ₂ = Δ₂} {Δ₃ = Δ₃} {l = l'} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} T σ ρ =
  fun-ext-h-ESub refl (cong (_◁ Γ₃) (assoc-sub-sub T σ* ρ*)) λ l T′ → λ where
  here →
    let
      F₁ = (Expr _ (Tsub ρ* (Tsub σ* T) ◁ Γ₃)) ; E₁ = (assoc-sub-sub T σ* ρ*) ; sub₁ = subst F₁ E₁
    in
    R.begin
      sub₁ (` here)
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      ` here
    R.≅⟨ H.cong {B = λ ■ → Expr _ (■ ◁ Γ₃) ■} (λ ■ → `_ {Γ = ■ ◁ Γ₃} {T = ■} here) (H.≡-to-≅ (assoc-sub-sub T σ* ρ*)) ⟩ 
      ` here
    R.≅⟨ refl ⟩
      Eliftₛ (σ* ∘ₛₛ ρ*) (σ >>SS ρ) l' T here
    R.∎
  (there x) →
    let
      F₁ = (Expr _ (Tsub ρ* (Tsub σ* T) ◁ Γ₃))                  ; E₁ = (assoc-sub-sub T′ σ* ρ*)                         ; sub₁ = subst F₁ E₁
      F₂ = (Expr _ (Tsub σ* T ◁ _))                             ; E₂ = (TidᵣT≡T (Tsub σ* T′))                           ; sub₂ = subst F₂ E₂
      F₃ = (Expr Δ₃ (Tsub (λ z x₁ → Tsub ρ* (σ* z x₁)) T ◁ Γ₃)) ; E₃ = (TidᵣT≡T (Tsub (λ z x₁ → Tsub ρ* (σ* z x₁)) T′)) ; sub₃ = subst F₃ E₃
      F₄ = (Expr Δ₃ Γ₃)                                         ; E₄ = E₁                                               ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Eliftₛ {T = T} σ* σ >>SS Eliftₛ ρ* ρ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (Esub ρ* (Eliftₛ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Esub ρ* (Eliftₛ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x)))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ (Tsub σ* T ◁ Γ₂)} (λ _ → Esub ρ* (Eliftₛ ρ* ρ))
                 (H.≡-to-≅ (sym (TidᵣT≡T (Tsub σ* T′)))) (H.≡-subst-removable F₂ E₂ _) ⟩
      Esub ρ* (Eliftₛ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))
    R.≅⟨ swap-Esub-Ewk ρ (Tsub σ* T) (σ l T′ x) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* (Tsub σ* T)} Tidᵣ Eidᵣ) (Esub ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong (λ ■ → Eren Tidᵣ (Ewkᵣ {T = ■} Tidᵣ Eidᵣ) (Esub ρ* ρ (σ l T′ x)))
                (H.≡-to-≅ (assoc-sub-sub T σ* ρ*)) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub (σ* ∘ₛₛ ρ*) T} Tidᵣ Eidᵣ) (Esub ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ))
                 (H.≡-to-≅ (assoc-sub-sub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
      Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Esub ρ* ρ (σ l T′ x)))
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Esub ρ* ρ (σ l T′ x))))
    R.≅⟨ refl ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) ((σ >>SS ρ) _ _ x))
    R.≅⟨ refl ⟩
      Ewk ((σ >>SS ρ) _ _ x)
    R.≅⟨ refl ⟩
      Eliftₛ {T = T} (σ* ∘ₛₛ ρ*) (σ >>SS ρ) l T′ (there x)
    R.∎

Esub↑-dist-∘ₛₛ-l :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
  Eliftₛ-l {l = l} σ* σ >>SS Eliftₛ-l ρ* ρ ≅ Eliftₛ-l {l = l} (σ* ∘ₛₛ ρ*) (σ >>SS ρ)
Esub↑-dist-∘ₛₛ-l {Δ₁} {Δ₂} {Δ₃} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l} σ ρ =
  fun-ext-h-ESub (sym (sub↑-dist-∘ₛₛ l σ* ρ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₁ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₁ = (assoc-sub-sub (Tren (Twkᵣ Tidᵣ) T′) (Tliftₛ σ* l) (Tliftₛ ρ* l)) ; sub₁ = subst F₁ E₁
        F₂ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₂ = (sym (swap-Tsub-Twk σ* T′))                                       ; sub₂ = subst F₂ E₂
        F₃ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₃ = (sym (swap-Tsub-Twk (σ* ∘ₛₛ ρ*) T′))                              ; sub₃ = subst F₃ E₃
        F₄ = (Expr Δ₃ Γ₃)              ; E₄ = (assoc-sub-sub T′ σ* ρ*)                                          ; sub₄ = subst F₄ E₄
      in
      R.begin
        (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) l′ (Twk T′) (tskip x)
      R.≅⟨ refl ⟩
        sub₁ (Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))))
      R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
        Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x)))
      R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₂) (l ◁* Γ₂)} (λ _ → Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ))
                   (H.≡-to-≅ (swap-Tsub-Twk σ* T′)) (H.≡-subst-removable F₂ E₂ _) ⟩
        Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))
      R.≅⟨ swap-Esub-Ewk-l ρ l (σ l′ T′ x) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (Esub ρ* ρ (σ l′ T′ x))
      R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l))
                   (H.≡-to-≅ (assoc-sub-sub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Esub ρ* ρ (σ l′ T′ x)))
      R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
        sub₃ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Esub ρ* ρ (σ l′ T′ x))))
      R.≅⟨ refl ⟩
        Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ) l′ (Twk T′) (tskip x)
      R.∎

mutual
  Eassoc-sub↑-sub↑-l :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
    Esub (Tliftₛ σ* l′ ∘ₛₛ Tliftₛ ρ* l′) (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) e ≅
    Esub (Tliftₛ (σ* ∘ₛₛ ρ*) l′) (Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
  Eassoc-sub↑-sub↑-l {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e σ ρ =
    R.begin
      Esub (Tliftₛ σ* l′ ∘ₛₛ Tliftₛ ρ* l′) (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Esub {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (sub↑-dist-∘ₛₛ l′ σ* ρ*))) (Esub↑-dist-∘ₛₛ-l σ ρ) ⟩
      Esub (Tliftₛ (σ* ∘ₛₛ ρ*) l′) (Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
    R.∎

  Eassoc-sub↑-sub↑ :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
    Esub ρ* (Eliftₛ {T = Tsub σ* T′} ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e) ≅
    Esub (σ* ∘ₛₛ ρ*) (Eliftₛ {T = T′} (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
  Eassoc-sub↑-sub↑ {Δ₃ = Δ₃} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e σ ρ =
    R.begin
      Esub ρ* (Eliftₛ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ Eassoc-sub-sub' e (Eliftₛ σ* σ) (Eliftₛ ρ* ρ) ⟩
      Esub (σ* ∘ₛₛ ρ*) ((Eliftₛ σ* σ) >>SS (Eliftₛ ρ* ρ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ESub (σ* ∘ₛₛ ρ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Esub (σ* ∘ₛₛ ρ*) ■ e)
                 (H.≡-to-≅ (assoc-sub-sub T′ σ* ρ*)) (Esub↑-dist-∘ₛₛ _ σ ρ) ⟩
      Esub (σ* ∘ₛₛ ρ*) (Eliftₛ (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
    R.∎

  Eassoc-sub-sub' : 
      {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃)
    → Esub ρ* ρ (Esub σ* σ e) ≅ Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e
  Eassoc-sub-sub' {Δ₁} {Δ₂} {Δ₃} {.zero} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) σ ρ =
    refl
  Eassoc-sub-sub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) σ ρ =
    let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-sub-sub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Esub ρ* ρ (Esub σ* σ (` x))
    R.≅⟨ refl ⟩
      Esub ρ* ρ (σ l T x)
    R.≅⟨ H.sym (H.≡-subst-removable F₁ E₁ _) ⟩
      sub₁ (Esub ρ* ρ (σ l T x))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (` x)
    R.∎
  Eassoc-sub-sub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) σ ρ =
    R.begin
      ƛ Esub ρ* (Eliftₛ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (assoc-sub-sub T₁ σ* ρ*))
                (H.≡-to-≅ (assoc-sub-sub T₂ σ* ρ*))
                (Eassoc-sub↑-sub↑ e σ ρ)  ⟩
      ƛ (Esub (σ* ∘ₛₛ ρ*) (Eliftₛ (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e)
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (ƛ e)
    R.∎
  Eassoc-sub-sub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) σ ρ =
    R.begin
      Esub ρ* ρ (Esub σ* σ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Esub ρ* ρ (Esub σ* σ e₁) · Esub ρ* ρ (Esub σ* σ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (assoc-sub-sub T σ* ρ*)) (H.≡-to-≅ (assoc-sub-sub T₁ σ* ρ*))
                (Eassoc-sub-sub' e₁ σ ρ) (Eassoc-sub-sub' e₂ σ ρ) ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e₁ · Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e₂
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (e₁ · e₂)
    R.∎
  Eassoc-sub-sub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) σ ρ =
    R.begin
      Esub ρ* ρ (Esub σ* σ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (assoc-sub-sub T (Tliftₛ σ* _) (Tliftₛ ρ* _)))
                 (Eassoc-sub-sub' e (Eliftₛ-l σ* σ) (Eliftₛ-l ρ* ρ)) ⟩
      Λ l ⇒ Esub (Tliftₛ σ* l ∘ₛₛ Tliftₛ ρ* l) (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ _ σ* ρ*))))
                 (Eassoc-sub↑-sub↑-l e σ ρ) ⟩
      Λ l ⇒ Esub (Tliftₛ (σ* ∘ₛₛ ρ*) l) (Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (Λ l ⇒ e)
    R.∎
  Eassoc-sub-sub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) σ ρ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tsub-[] σ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tsub-[] (σ* ∘ₛₛ ρ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tsub-[] ρ* (Tsub (Tliftₛ σ* _) T) (Tsub σ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Esub ρ* ρ (Esub σ* σ (e ∙ T′))
    R.≅⟨ refl ⟩
      Esub ρ* ρ (sub₂ (Esub σ* σ e ∙ Tsub σ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Esub ρ* ρ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Esub ρ* ρ (Esub σ* σ e ∙ Tsub σ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Esub ρ* ρ (Esub σ* σ e) ∙ Tsub ρ* (Tsub σ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Esub ρ* ρ (Esub σ* σ e) ∙ Tsub ρ* (Tsub σ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-sub↑-sub↑ T σ* ρ*)) (Eassoc-sub-sub' e σ ρ) (H.≡-to-≅ (assoc-sub-sub T′ σ* ρ*)) ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e ∙ Tsub (σ* ∘ₛₛ ρ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e ∙ (Tsub (σ* ∘ₛₛ ρ*) T′))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (e ∙ T′)
    R.∎ 

-- TODO: The following lemmas are only for backwards-compatibility with HEq

Eassoc-ren-ren : 
    {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → (e : Expr Δ₁ Γ₁ T)
  → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃)
  → let sub = subst (Expr Δ₃ Γ₃) (assoc-ren-ren T ρ* σ*) in
    sub (Eren σ* σ (Eren ρ* ρ e)) ≡ Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e
Eassoc-ren-ren {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} e ρ σ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-ren-ren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Eren σ* σ (Eren ρ* ρ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Eren σ* σ (Eren ρ* ρ e)
    R.≅⟨ Eassoc-ren-ren' e ρ σ ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e
    R.∎
  )

Eassoc-sub-ren : 
    {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → (e : Expr Δ₁ Γ₁ T)
  → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃)
  → let sub = subst (Expr Δ₃ Γ₃) (assoc-sub-ren T ρ* σ*) in
    sub (Esub σ* σ (Eren ρ* ρ e)) ≡ Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e
Eassoc-sub-ren {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} e ρ σ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-sub-ren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Esub σ* σ (Eren ρ* ρ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Esub σ* σ (Eren ρ* ρ e)
    R.≅⟨ Eassoc-sub-ren' e ρ σ ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e
    R.∎
  )

Eassoc-ren-sub : 
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    {T : Type Δ₁ l}
    (e : Expr Δ₁ Γ₁ T)
    (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
  let sub = subst (Expr Δ₃ Γ₃) (assoc-ren-sub T σ* ρ*) in
  sub (Eren ρ* ρ (Esub σ* σ e)) ≡ Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e
Eassoc-ren-sub {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} e σ ρ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-ren-sub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Eren ρ* ρ (Esub σ* σ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Eren ρ* ρ (Esub σ* σ e)
    R.≅⟨ Eassoc-ren-sub' e σ ρ ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e
    R.∎
  )

Eassoc-sub-sub : 
    {σ₁* : TSub Δ₁ Δ₂}{σ₂* : TSub Δ₂ Δ₃}
  → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
  → {T : Type Δ₁ l}
  → (e : Expr Δ₁ Γ₁ T)
  → (σ₁ : ESub σ₁* Γ₁ Γ₂) → (σ₂ : ESub σ₂* Γ₂ Γ₃)
  → let sub = subst (Expr Δ₃ Γ₃) (assoc-sub-sub T σ₁* σ₂*) in
    sub (Esub σ₂* σ₂ (Esub σ₁* σ₁ e)) ≡ Esub (σ₁* ∘ₛₛ σ₂*) (σ₁ >>SS σ₂) e
Eassoc-sub-sub {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} e σ ρ =
  let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (assoc-sub-sub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
  H.≅-to-≡ (
    R.begin
      sub₁ (Esub ρ* ρ (Esub σ* σ e))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Esub ρ* ρ (Esub σ* σ e)
    R.≅⟨ Eassoc-sub-sub' e σ ρ ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e
    R.∎
  )

--------------------------------------------------------------------------------

TSub-id-right : ∀ (σ* : TSub Δ₁ Δ₂) → (σ* ∘ₛₛ Tidₛ) ≡ σ*
TSub-id-right {Δ₁ = Δ₁} σ* = fun-ext₂ aux
  where
    aux : (l : Level) (x : l ∈ Δ₁) → (σ* ∘ₛₛ Tidₛ) l x ≡ σ* l x
    aux l x = TidₛT≡T (σ* l x)

TSub-id-left :  ∀ (σ* : TSub Δ₁ Δ₂) → (Tidₛ ∘ₛₛ σ*) ≡ σ*
TSub-id-left {Δ₁} σ* = fun-ext₂ λ x y → refl
  where
    aux : (l : Level) (x : l ∈ Δ₁) → (Tidₛ ∘ₛₛ σ*) l x ≡ σ* l x
    aux l x = refl

wklift~id : {e : Expr Δ Γ (Tsub Tidₛ T′)} → (Ewkᵣ Tidᵣ Eidᵣ >>RS sub0 {T₁ = T′} e) ~ (Eidₛ >>SS Eidₛ)
wklift~id {Δ = Δ}{Γ = Γ}{e = e} l T′ x =
  let
    F = Expr Δ Γ
    E₁ = assoc-sub-ren T′ Tidᵣ Tidₛ
    E₂ = assoc-sub-sub T′ Tidₛ Tidₛ
    context₁ = λ {T : Type Δ l} → Esub{Γ₁ = Γ}{Γ₂ = Γ}{T = T} Tidₛ Eidₛ
    context₂ = λ {T : Type Δ l} → Eidₛ{Γ = Γ} l T
  in
  begin
    subst F E₁ (((Eidₛ l (Tren Tidᵣ T′)) (subst (λ T → inn T _) (sym (TidᵣT≡T T′)) x)))
  ≡⟨ cong (subst F E₁)
    (dist-subst' {F = (λ T → inn T _)}{G = F} (Tsub Tidₛ) context₂ (sym (TidᵣT≡T T′)) (cong (Tsub Tidₛ) (sym (TidᵣT≡T T′))) x) ⟩
    subst F E₁ (subst F (cong (Tsub Tidₛ) (sym (TidᵣT≡T T′))) (Eidₛ l T′ x))
  ≡⟨ refl ⟩
    subst F E₁ (subst F (cong (Tsub Tidₛ) (sym (TidᵣT≡T T′))) (subst F (sym (TidₛT≡T T′)) (` x)))
  ≡⟨  subst*-irrelevant (⟨ F , sym (TidₛT≡T T′) ⟩∷ ⟨ F , cong (Tsub Tidₛ) (sym (TidᵣT≡T T′)) ⟩∷ ⟨ F , E₁ ⟩∷ [])
                        (⟨ F , sym (TidₛT≡T T′) ⟩∷ ⟨ F , cong (Tsub Tidₛ) (sym (TidₛT≡T T′)) ⟩∷ ⟨ F , E₂ ⟩∷ [] ) (` x) ⟩
    subst F E₂ (subst F (cong (Tsub Tidₛ) (sym (TidₛT≡T T′))) (subst F (sym (TidₛT≡T T′)) (` x)))
  ≡⟨ refl ⟩
    subst F E₂ (subst F (cong (Tsub Tidₛ) (sym (TidₛT≡T T′))) (context₁ (` x)))
  ≡⟨ cong (subst F E₂)
     (sym (dist-subst' {F = F}{G = F} (Tsub Tidₛ) context₁ (sym (TidₛT≡T T′)) (cong (Tsub Tidₛ) (sym (TidₛT≡T T′))) (` x))) ⟩
    subst F E₂ (context₁ (subst F (sym (TidₛT≡T T′)) (` x)))
  ≡⟨ refl ⟩
    subst F E₂ (Esub Tidₛ Eidₛ (Eidₛ l T′ x))
  ∎

-- σT≡TextₛσTwkT : {T′ : Type Δ₂ l′} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) → Tsub (Textₛ σ T′) (Twk T) ≡ Tsub σ T
-- σT≡TextₛσTwkT {T′ = T′} σ T = begin 
--     Tsub (Textₛ σ _) (Twk T)
--   ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Textₛ σ _) ⟩
--     Tsub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′) T
--   ≡⟨ sym (assoc-sub-sub T _ σ) ⟩
--     Tsub σ (Tsub Tidₛ T)
--   ≡⟨ cong (λ T → Tsub σ T) (TidₛT≡T T) ⟩
--     Tsub σ T
--   ∎
ext-wk-e≡e : ∀ {Δ}{Γ}{l′}{T′ : Type Δ l′}{l}{T : Type Δ l} → 
  (e′ : Expr Δ Γ (Tsub Tidₛ T′)) (e : Expr Δ Γ T) → 
  Esub Tidₛ (sub0 {T₁ = T′} e′) (Ewk e) ≡ subst (Expr Δ Γ) (sym (TidₛT≡T T)) e
ext-wk-e≡e {T′ = T′} {T = T} e′ e = 
  let asr = Eassoc-sub-ren e (Ewkᵣ Tidᵣ Eidᵣ) (sub0 {T₁ = T′} e′) in
  let ass = sym (Eassoc-sub-sub e Eidₛ Eidₛ) in
  begin 
    Esub Tidₛ (sub0 {T₁ = T′} e′) (subst (Expr _ _) (TidᵣT≡T T) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e))
  ≡⟨ dist-subst' {F = Expr _ _} {G = Expr _ _} (λ T → Tsub Tidₛ T) (Esub Tidₛ (sub0 {T₁ = T′} e′)) (TidᵣT≡T T) (assoc-sub-ren T Tidᵣ Tidₛ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e) ⟩ 
    (subst (Expr _ _) (assoc-sub-ren T Tidᵣ Tidₛ) (Esub Tidₛ (sub0 {T₁ = T′} e′) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e)))
  ≡⟨ asr ⟩ 
    Esub Tidₛ (Ewkᵣ Tidᵣ Eidᵣ >>RS sub0 {T₁ = T′} e′) e
  ≡⟨ Esub~ (Ewkᵣ Tidᵣ Eidᵣ >>RS sub0 {T₁ = T′} e′) (Eidₛ >>SS Eidₛ) (wklift~id {T′ = T′} {e = e′}) e ⟩
    Esub Tidₛ (Eidₛ >>SS Eidₛ) e
  ≡⟨ ass ⟩ 
    subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ)
      (Esub Tidₛ Eidₛ (Esub Tidₛ Eidₛ e))
  ≡⟨ cong (subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ)) (Eidₛe≡e (Esub Tidₛ Eidₛ e)) ⟩ 
    subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (subst (Expr _ _) (sym (TidₛT≡T _)) (Esub Tidₛ Eidₛ e))
  ≡⟨ cong (λ e → subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (subst (Expr _ _) (sym (TidₛT≡T _)) e)) (Eidₛe≡e e) ⟩
    subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (subst (Expr _ _) (sym (TidₛT≡T (Tsub Tidₛ T))) (subst (Expr _ _) (sym (TidₛT≡T T)) e)) 
  ≡⟨ elim-subst (Expr _ _) (assoc-sub-sub T Tidₛ Tidₛ) (sym (TidₛT≡T (Tsub Tidₛ T))) (subst (Expr _ _) (sym (TidₛT≡T T)) e) ⟩ 
    subst (Expr _ _) (sym (TidₛT≡T T)) e
  ∎
-- ext=lift∘single~
Eext-Elift~ : ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
  → let r = Eliftₛ {T = T} σ* σ >>SS sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
    let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
    Eextₛ {T = T} σ* σ e′ ~ subᵣ r
Eext-Elift~ {.l₁} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ (.T) here =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ σ* → Tsub σ* T) (TSub-id-right σ*)) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T  σ* Tidₛ) in
  begin
    e′
      ≡⟨ sym (elim-subst₃ (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T) (TSub-id-right σ*)) (assoc-sub-sub T  σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T))) e′) ⟩
    sub₁′ (sub₃ (sub₂ e′))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub {T = Tsub σ* T} _ (sub0 (sub₂ e′)) (` here)))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub {T = Tsub σ* T} _ (sub0 (sub₂ e′)) ((Eliftₛ {T = T} σ* σ) l₁ _ here)))
      ≡⟨⟩
    sub₁′ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ here)
      ≡⟨ sym (dist-subst' {F = (λ a → ESub a (T ◁ Γ₁) Γ₂)} {G = Expr Δ₂ Γ₂}
                          (λ τ* → Tsub τ* T)
                          (λ f → f l₁ _ here)
                          (TSub-id-right σ*)
                          (cong (λ σ*₁ → Tsub σ*₁ T) (TSub-id-right σ*))
                          (Eliftₛ σ* σ >>SS sub0 (subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) e′)))
       ⟩
    sub₁ (Eliftₛ σ* σ >>SS sub0 (sub₂ e′)) l₁ _ here 
  ∎
Eext-Elift~ {l} {Δ₁} {Δ₂} {σ* = σ*} {Γ₁} {Γ₂} {T = T} σ e′ l₁ T₁ (there x) =
  let sub₁ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
  let sub₁′ = subst (Expr Δ₂ Γ₂) (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*)) in
  let sub₁″ = subst (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁)) (TSub-id-right σ*) in
  let sub₂ = subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T (Tsub σ* T))) in
  let sub₃ = subst (Expr Δ₂ Γ₂) (assoc-sub-sub T₁ σ* Tidₛ) in
  sym $ begin
    sub₁ (Eliftₛ σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x)
      ≡⟨ dist-subst' {F = (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂)} {G = (λ τ* → Expr Δ₂ Γ₂ (Tsub τ* T₁))} id (λ τ → τ l₁ _ (there x)) (TSub-id-right σ*) (TSub-id-right σ*) (Eliftₛ σ* σ >>SS sub0 (sub₂ e′)) ⟩
    sub₁″ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨ sym (subst-cong (Expr Δ₂ Γ₂) (λ τ* → Tsub τ* T₁) (TSub-id-right σ*) ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))) ⟩ 
    sub₁′ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨⟩
    sub₁′ ((Eliftₛ {T = T} σ* σ >>SS sub0 (sub₂ e′)) l₁ _ (there x))
      ≡⟨⟩
    sub₁′ (sub₃ (Esub _ (sub0 ( sub₂ e′)) (Eliftₛ {T = T} σ* σ l₁ _ (there x))))
      ≡⟨ cong sub₁′ (cong sub₃ (ext-wk-e≡e {l′ = l} (sub₂ e′) (σ l₁ _ x))) ⟩
    sub₁′ (sub₃ ((subst (Expr Δ₂ Γ₂) (sym (TidₛT≡T _)) (σ l₁ _ x))))
      ≡⟨ elim-subst₃ (Expr Δ₂ Γ₂)
           (cong (λ τ* → Tsub τ* T₁) (TSub-id-right σ*))
           (assoc-sub-sub T₁ σ* Tidₛ) (sym (TidₛT≡T (Tsub σ* T₁))) (σ l₁ _ x)
       ⟩
    σ l₁ _ x
  ∎

-- ext=lift∘single
Eext-Elift :   ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} {Tₑ : Type Δ₁ l₁} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T)) (e : Expr Δ₁ (T ◁ Γ₁) Tₑ)
  → let r = Eliftₛ {T = T} σ* σ >>SS sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
    let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
    Esub σ* (Eextₛ {T = T} σ* σ e′) e ≡ Esub σ* (subᵣ r) e
Eext-Elift {σ* = σ*}{Γ₁}{Γ₂} {T = T} σ e′ e = Esub~ (Eextₛ σ* σ e′)
                                                (subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*)
                                                 (Eliftₛ {T = T} σ* σ >>SS
                                                  sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′)))
                                                (Eext-Elift~ σ e′) e

-- Eext-Elift-l~ : ∀ {l}{Δ₁}{Δ₂} {σ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} (σ : ESub σ* Γ₁ Γ₂) (e′ : Expr Δ₂ Γ₂ (Tsub σ* T))
--   → let r = Eliftₛ {T = T} σ* σ >>SS sub0 (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) e′) in
--     let subᵣ = subst (λ τ* → ESub τ* (T ◁ Γ₁) Γ₂) (TSub-id-right σ*) in
--     Eextₛ {T = T} σ* σ e′ ~ subᵣ r
-- Eext-Elift-l~ = {!   !}

EliftₛEextₛ~ :  {Γ : TEnv Δ} (l l′ : Level) (T′ : Type [] l) (T : Type (l ∷ Δ) l′) (τ* : TSub Δ []) (σ : ESub τ* Γ ∅)
  → ((Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ)) ~[ Tliftₛ∘Textₛ l τ* T′ ]~ (Eextₛ-l τ* σ)
EliftₛEextₛ~ l l′ T′ T τ* σ l₁ .(Twk _) (tskip {T = T₁} x) =
  let
    F₁ = (Expr _ _)  ; E₁ = (assoc-sub-sub (Twk T₁) (Tliftₛ τ* l) (Textₛ Tidₛ T′))        ; sub₁ = subst F₁ E₁
    F₂ = (Expr _ _)  ; E₂ = (sym (swap-Tsub-Twk τ* T₁))                                  ; sub₂ = subst F₂ E₂
    F₃ = (Expr [] ∅) ; E₃ = (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T₁)))    ; sub₃ = subst F₃ E₃
    F₄ = (Expr [] ∅) ; E₄' = (assoc-sub-ren (Tsub τ* T₁) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′))     ; E₄ = (sym E₄') ; sub₄ = subst F₄ E₄
    F₅ = (Expr [] ∅) ; E₅ = (cong (λ σ* → Tsub σ* (Twk T₁)) (sym (Tliftₛ∘Textₛ l τ* T′))) ; sub₅ = subst F₅ E₅
    F₆ = (Expr _ _)  ; E₆ = (sym (σT≡TextₛσTwkT τ* T₁))                                   ; sub₆ = subst F₆ E₆
    F₇ = (Expr _ _)  ; E₇ = (sym (TidₛT≡T (Tsub τ* T₁)))                                  ; sub₇ = subst F₇ E₇

    F₁' = (Expr [] ∅) ; E₁' = λ l₂ T₂ x₁ →(assoc-sub-ren T₂ (λ z x₂ → there x₂) (Textₛ Tidₛ T′)) ; sub₁' = λ l₂ T₂ x₁ → subst F₁' (E₁' l₂ T₂ x₁)
    F₂' = (Expr [] ∅) ; E₂' = λ l₂ T₂ x₁ →(sym
                                (trans (assoc-sub-ren T₂ (λ z x₂ → there x₂) (Textₛ Tidₛ T′))
                                (trans (sym (assoc-sub-sub T₂ Tidₛ Tidₛ))
                                  (trans (cong (Tsub Tidₛ) (TidₛT≡T T₂)) refl))))
                                ; sub₂' = λ l₂ T₂ x₁ → subst F₂' (E₂' l₂ T₂ x₁)
    F₃' = (Expr [] ∅) ; E₃' = λ l₂ T₂ → (sym (TidₛT≡T T₂)) ; sub₃' = λ l₂ T₂ → subst F₃' (E₃' l₂ T₂)
  in
  begin
    (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) l₁ (Twk _) (tskip x)
  ≡⟨ refl ⟩
    sub₁ (Esub _ (Eextₛ-l Tidₛ Eidₛ) ((Eliftₛ-l τ* σ) _ _ (tskip x)))
  ≡⟨ refl ⟩
    sub₁ (Esub _ (Eextₛ-l Tidₛ Eidₛ) (sub₂ (Ewk-l (σ _ _ x))))
  ≡⟨ cong sub₁ (dist-subst' {F = F₂} {G = F₃} (Tsub (Textₛ Tidₛ T′))
                            (Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ)) E₂ E₃ (Ewk-l (σ _ _ x))) ⟩
    sub₁ (sub₃ (Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ) (Ewk-l (σ _ _ x))))
  ≡⟨ cong (λ H → sub₁ (sub₃ H))
          (subst-swap {F = F₃} E₄'
             (Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ) (Eren (Twkᵣ Tidᵣ) (λ z z₁ → tskip) (σ l₁ T₁ x)))
             (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′) ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) (σ l₁ T₁ x))
             (Eassoc-sub-ren (σ _ _ x) (λ _ _ → tskip) (Eextₛ-l Tidₛ Eidₛ)) ) ⟩
    sub₁ (sub₃ (sub₄ (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′)
                           ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ)
                           (σ l₁ T₁ x))))
  ≡⟨ refl ⟩
    sub₁ (sub₃ (sub₄ (Esub Tidₛ (λ l₂ T₂ x₁ → sub₁' l₂ T₂ x (sub₂' l₂ T₂ x (sub₃' l₂ T₂ (` x₁)))) (σ l₁ T₁ x))))
  ≡⟨ cong (λ ■ → sub₁ (sub₃ (sub₄ (Esub Tidₛ ■ (σ l₁ T₁ x)))))
          (fun-ext λ l₂ → fun-ext λ T₂ → fun-ext λ x₁ →
              elim-subst F₁' (E₁' l₂ T₂ x) (E₂' l₂ T₂ x) (sub₃' l₂ T₂ (` x₁)) ) ⟩
    sub₁ (sub₃ (sub₄ (Esub Tidₛ (λ l₂ T₂ x₁ → (sub₃' l₂ T₂ (` x₁))) (σ l₁ T₁ x))))
  ≡⟨ refl ⟩
    sub₁ (sub₃ (sub₄ (Esub Tidₛ Eidₛ (σ l₁ T₁ x))))
  ≡⟨ cong (λ ■ → sub₁ (sub₃ (sub₄ ■))) (Eidₛe≡e (σ l₁ T₁ x)) ⟩
    sub₁ (sub₃ (sub₄ (sub₇ (σ l₁ T₁ x))))
  ≡⟨ subst*-irrelevant (⟨ F₇ , E₇ ⟩∷ ⟨ F₄ , E₄ ⟩∷ ⟨ F₃ , E₃ ⟩∷ ⟨ F₁ , E₁ ⟩∷ [])
                       (⟨ F₆ , E₆ ⟩∷ ⟨ F₅ , E₅ ⟩∷ [])
                       (σ l₁ T₁ x) ⟩
    sub₅ (sub₆ (σ l₁ T₁ x))
  ≡⟨ refl ⟩
    sub₅ (Eextₛ-l τ* σ l₁ (Twk T₁) (tskip x))
  ∎

Elift-l-[]≡Eext : {Γ : TEnv Δ} (l l′ : Level) (T′ : Type [] l) (T : Type (l ∷ Δ) l′) (τ* : TSub Δ []) (σ : ESub τ* Γ ∅) (e : Expr (l ∷ Δ) (l ◁* Γ) T)
  → let sub = subst (Expr [] ∅) (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T)) in
    ((Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e) [ T′ ]ET) ≡ sub (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e)
Elift-l-[]≡Eext l l′ T′ T τ* σ e =
  let
    F₁ = (Expr [] ∅) ; E₁ = (sym (assoc-sub-sub T (Tliftₛ τ* l) (Textₛ Tidₛ T′)))  ; sub₁ = subst F₁ E₁
    F₂ = (Expr [] ∅) ; E₂ = (sym (σ↑T[T′]≡TextₛσT′T τ* T′ T))                      ; sub₂ = subst F₂ E₂
    F₃ = (Expr [] ∅) ; E₃ = (cong (λ σ* → Tsub σ* T) (sym (Tliftₛ∘Textₛ l τ* T′))) ; sub₃ = subst F₃ E₃
  in
  begin
    (Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e [ T′ ]ET)
  ≡⟨ subst-swap (assoc-sub-sub T (Tliftₛ τ* l) (Textₛ Tidₛ T′))
      (Esub (Textₛ Tidₛ T′) (Eextₛ-l Tidₛ Eidₛ) (Esub (Tliftₛ τ* l) (Eliftₛ-l τ* σ) e))
      (Esub (Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′) (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) e)
      (Eassoc-sub-sub e (Eliftₛ-l τ* σ) (Eextₛ-l Tidₛ Eidₛ)) ⟩
    sub₁ (Esub (Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′) (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) e)
  ≡⟨ cong sub₁ (Esub~~ (Tliftₛ∘Textₛ l τ* T′) (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) (Eextₛ-l τ* σ) (EliftₛEextₛ~ _ _ T′ T τ* σ) e) ⟩
    sub₁ (sub₃ (Esub (Textₛ τ* T′) (λ l₁ T₁ z → Eextₛ-l τ* σ l₁ T₁ z) e))
  ≡⟨ subst*-irrelevant (⟨ F₃ , E₃ ⟩∷ ⟨ F₁ , E₁ ⟩∷ []) (⟨ F₂ , E₂ ⟩∷ []) _ ⟩
    sub₂ (Esub (Textₛ τ* T′) (Eextₛ-l τ* σ) e)
  ∎

-- let eqσ : Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′ ≡ Tidσ
equal-Esub-wk>>lift : ∀ {Γ : TEnv []} (T′ : Type [] l)
  → _~_ {Γ₁ = Γ} ((λ z z₁ → tskip) >>RS Eextₛ-l {T = T′} Tidₛ Eidₛ) Eidₛ
equal-Esub-wk>>lift T′ l T x =
  begin
    ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) l T x
  ≡⟨⟩
    subst (Expr [] _)
      (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
      (subst (Expr [] _)
       (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
       (Eidₛ l T x))
  ≡⟨ subst-subst (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
          {(assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))}
          {Eidₛ l T x} ⟩
    subst (Expr [] _)
      (trans
       (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
       (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′)))
      (Eidₛ l T x)
  ≡⟨ subst-irrelevant
      (trans
       (sym
        (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′))
         (trans (sym (assoc-sub-sub T (λ z → `_) (λ z → `_)))
          (trans (cong (Tsub (λ z → `_)) (TidₛT≡T T)) refl))))
       (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ (λ z → `_) T′)))
       refl
       (Eidₛ l T x) ⟩
    Eidₛ l T x
  ∎

-- let eqσ : Tliftₛ τ* l ∘ₛₛ Textₛ Tidₛ T′ ≡ Textₛ τ* T′
equal-ESub : ∀ {Γ : TEnv Δ} (T′ : Type [] l) (τ* : TSub Δ []) (σ : ESub τ* Γ ∅)
  → (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) ~[ Tliftₛ∘Textₛ l τ* T′ ]~ Eextₛ-l τ* σ
equal-ESub T′ τ* σ l .(Twk _) (tskip {T = T} x) =
  begin
    (Eliftₛ-l τ* σ >>SS Eextₛ-l Tidₛ Eidₛ) l (Twk T) (tskip x)
  ≡⟨ refl ⟩
    subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (Esub _ (Eextₛ-l Tidₛ Eidₛ) (Eliftₛ-l τ* σ _ _ (tskip x)))
  ≡⟨ refl ⟩
    subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
    (Esub _ (Eextₛ-l Tidₛ Eidₛ) (subst (Expr _ _) (sym (swap-Tsub-Twk τ* T)) (Ewk-l (σ _ _ x))))
  ≡⟨ cong (subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))
          (dist-subst' {F = Expr _ _} {G = Expr [] ∅} (λ T₁ → T₁ [ T′ ]T) (Esub _ (Eextₛ-l Tidₛ Eidₛ))
                   (sym (swap-Tsub-Twk τ* T))
                   (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
                   (Ewk-l (σ _ _ x))) ⟩
    subst (Expr _ _) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
    (subst (Expr [] ∅) (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
      (Esub _ (Eextₛ-l Tidₛ Eidₛ) (Ewk-l (σ _ _ x))))
  ≡⟨ cong
       (λ E →
          subst (Expr _ _)
          (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
          (subst (Expr [] ∅)
           (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T))) E))
       (subst-swap (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′))
          (Esub _ (Eextₛ-l Tidₛ Eidₛ) (Ewk-l (σ _ _ x)))
          (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′)
           ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) (σ l T x))
          (Eassoc-sub-ren (σ l T x) (λ _ _ → tskip) (Eextₛ-l Tidₛ Eidₛ)))
    ⟩
    subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′)
         ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) (σ l T x))))
  ≡⟨ cong (λ E → subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        E)))
     (Esub~ ((λ z z₁ → tskip) >>RS Eextₛ-l Tidₛ Eidₛ) Eidₛ (equal-Esub-wk>>lift T′) (σ l T x))
   ⟩
    subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (Esub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ Tidₛ T′) Eidₛ (σ l T x))))
  ≡⟨ cong (λ E → subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        E)))
        (Eidₛe≡e (σ l T x)) ⟩
    subst (Expr [] ∅)
      (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))
      (subst (Expr [] ∅)
       (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
       (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x))))
  ≡⟨ subst-subst (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
     {(assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))}
     {(subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x)))} ⟩
    subst (Expr [] ∅)
      (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T))) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))
      (subst (Expr [] ∅)
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x)))
  ≡⟨ subst-subst (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
         {(trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T))) (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))}
         {(subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x))} ⟩
    subst (Expr [] ∅)
      (trans
       (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
       (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
        (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))))
      (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub τ* T))) (σ l T x))
  ≡⟨ subst-subst (sym (TidₛT≡T (Tsub τ* T)))
                  {(trans
       (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
       (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
        (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′))))}
                   {(σ l T x)} ⟩
    subst (Expr [] ∅)
      (trans (sym (TidₛT≡T (Tsub τ* T)))
       (trans
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
         (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))))
      (σ l T x)
  ≡⟨ subst-irrelevant
       (trans (sym (TidₛT≡T (Tsub τ* T)))
       (trans
        (sym (assoc-sub-ren (Tsub τ* T) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T′)))
        (trans (cong (Tsub (Textₛ Tidₛ T′)) (sym (swap-Tsub-Twk τ* T)))
         (assoc-sub-sub (Twk T) (Tliftₛ τ* _) (Textₛ Tidₛ T′)))))
       (trans (sym (σT≡TextₛσTwkT τ* T))
       (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′))))
       (σ l T x) ⟩
    subst (Expr [] ∅)
      (trans (sym (σT≡TextₛσTwkT τ* T))
       (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′))))
      (σ l T x)
  ≡⟨ sym (subst-subst (sym (σT≡TextₛσTwkT τ* T))
           {(cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′)))}
           {(σ _ _ x)}) ⟩
    subst (Expr [] ∅) (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′)))
      (subst (Expr _ _) (sym (σT≡TextₛσTwkT τ* T)) 
        (σ _ _ x))
  ≡⟨ refl ⟩
    subst (Expr [] ∅)
      (cong (λ σ* → Tsub σ* (Twk T)) (sym (Tliftₛ∘Textₛ _ τ* T′)))
      (Eextₛ-l τ* σ l (Twk T) (tskip x))
  ∎

----------------------------------------------------------------------

-- semantic renamings on expression
ERen* : {ρ* : TRen Δ₁ Δ₂} (TRen* : TRen* ρ* η₁ η₂) → (ρ : ERen ρ* Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → Setω
ERen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ*} Tren* ρ γ₁ γ₂ = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ _ _ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ _ _ x)
-- γ* l (Tren Tidᵣ T₁) (Eidᵣ l T₁ x) ≡
--       subst id (sym (Tren*-preserves-semantics (Tren*-id η) T₁))
--       (γ* l T₁ x)
Ewk∈ERen* : ∀ {T : Type Δ l} (γ : Env Δ Γ η) (⟦e⟧ : ⟦ T ⟧ η) →  
  ERen* (Tren*-id η) (Ewkᵣ {T = T} Tidᵣ Eidᵣ) γ (extend γ ⟦e⟧) 
Ewk∈ERen* {η = η} γ* ⟦e⟧ {T = T} x = begin 
    γ* _ (Tren Tidᵣ T) (subst (λ T → inn T _) (sym (TidᵣT≡T T)) x)
  ≡⟨ {!   !} ⟩
    subst id (sym (Tren*-preserves-semantics (Tren*-id η) T)) (γ* _ T x)
  ∎ 
ERen*-lift : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦e⟧ : ⟦ Tren ρ* T ⟧ η₂) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* Tren* (Eliftᵣ {T = T} _ ρ) (extend γ₁ (subst id (Tren*-preserves-semantics Tren* T) ⟦e⟧)) (extend γ₂ ⟦e⟧)
ERen*-lift {η₁ = η₁} {η₂ = η₂} {T = T} {ρ* = ρ*} ⟦e⟧ Tren* Eren* here 
  rewrite Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T = refl
ERen*-lift {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} ⟦e⟧ Tren* Eren* {T = T} (there x) = Eren* x

ERen*-lift-l : ∀ {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} → 
  (⟦α⟧ : Set l) →
  (Tren* : TRen* ρ* η₁ η₂) → 
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  ERen* (Tren*-lift ⟦α⟧ Tren*) (Eliftᵣ-l _ ρ) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₁) (extend-tskip {⟦α⟧  = ⟦α⟧} γ₂)
ERen*-lift-l {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {l = l₁} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦α⟧ Tren* Eren* {l} (tskip {T = T} x) =
  let eq* = Eren* x in 
  let eq = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) (Twk T)) in 
  let eq' = sym (Tren*-preserves-semantics (wkᵣ∈Ren* η₁ ⟦α⟧) T) in 
  let eq'' = sym (Tren*-preserves-semantics {ρ* = ρ*} {η₂ = η₂} Tren* T) in
  let eq₁ = cong (λ T₁ → inn T₁ (l₁ ◁* Γ₂)) (sym (swap-Tren-Twk ρ* T)) in
  let eq₂ = (cong (λ T → ⟦ T ⟧ (⟦α⟧ ∷ η₂)) (sym (swap-Tren-Twk ρ* T))) in
  let eq′ = trans (sym eq'') (trans eq' eq) in
  begin 
    extend-tskip γ₂ _ (Tren (Tliftᵣ ρ* l₁) (Twk T)) (subst id eq₁ (tskip (ρ _ T x)))
  ≡⟨ {! !} ⟩ -- dist subst -- 
    subst id eq₂ (extend-tskip γ₂ _ (Twk (Tren ρ* T)) (tskip (ρ _ _ x)))
  ≡⟨⟩ 
    subst id eq₂ (subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T))) (γ₂ l (Tren ρ* T) (ρ _ _ x)))
  ≡⟨ subst-shuffle′′′′ ((γ₂ l (Tren ρ* T) (ρ _ _ x))) eq₂ ((sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η₂} {⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) (Tren ρ* T)))) eq′ refl ⟩ 
    subst id eq′ (γ₂ l (Tren ρ* T) (ρ _ _ x))
  ≡⟨ cong (subst id eq′) eq* ⟩
    subst id eq′ (subst id eq'' (γ₁ l T x))
  ≡⟨ subst-shuffle′′′′ (γ₁ l T x) eq′ eq'' eq eq' ⟩
    subst id eq (subst id eq' (γ₁ l T x))
  ∎

Eren*-preserves-semantics : ∀ {T : Type Δ₁ l} {ρ* : TRen Δ₁ Δ₂} {ρ : ERen ρ* Γ₁ Γ₂} {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} →
  (Tren* : TRen* ρ* η₁ η₂) →
  (Eren* : ERen* Tren* ρ γ₁ γ₂) → 
  (e : Expr Δ₁ Γ₁ T) → 
  E⟦ Eren ρ* ρ e ⟧ η₂ γ₂ ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (E⟦ e ⟧ η₁ γ₁)
Eren*-preserves-semantics Tren* Eren* (# n) = refl
Eren*-preserves-semantics Tren* Eren* (` x) = Eren* x
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(T ⇒ T′)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (ƛ_ {T = T} {T′} e) = fun-ext λ ⟦e⟧ →
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ ρ* ρ} {γ₂ = extend γ₂ ⟦e⟧} Tren* (ERen*-lift {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} ⟦e⟧ Tren* Eren*) e  in
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = Tren*-preserves-semantics Tren* T in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren ρ* (Eliftᵣ ρ* ρ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ η₁ (extend γ₁ (subst id eq₁ ⟦e⟧)))
  ≡⟨ dist-subst (λ ⟦e⟧ → E⟦ e ⟧ η₁ (extend γ₁ ⟦e⟧)) eq₁ eq eq₂ ⟦e⟧ ⟩
    subst id eq (λ ⟦e⟧ → E⟦ e ⟧ η₁ (extend γ₁ ⟦e⟧)) ⟦e⟧
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_·_ {T = T} {T′ = T′} e₁ e₂) =
  let eq₁* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e₁ in
  let eq₂* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e₂ in
  let eq = sym (Tren*-preserves-semantics Tren* (T ⇒ T′)) in
  let eq₁ = sym (Tren*-preserves-semantics Tren* T) in
  let eq₂ = sym (Tren*-preserves-semantics Tren* T′) in
  begin 
    E⟦ Eren _ ρ e₁ ⟧ η₂ γ₂ (E⟦ Eren _ ρ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ η₁ γ₁)) (subst id eq₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ η₁ γ₁) eq₁ eq eq₂ (E⟦ e₂ ⟧ η₁ γ₁) ⟩
    subst id eq₂ (E⟦ e₁ ⟧ η₁ γ₁ (E⟦ e₂ ⟧ η₁ γ₁))
  ∎
Eren*-preserves-semantics {η₁ = η₁} {η₂ = η₂} {T = .(`∀α l , T)} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Eren*-preserves-semantics {ρ = Eliftᵣ-l _ ρ} {γ₁ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₁} {γ₂ = extend-tskip {⟦α⟧ = ⟦α⟧} γ₂} 
            (Tren*-lift {η₁ = η₁} ⟦α⟧ Tren*) (ERen*-lift-l ⟦α⟧ Tren* Eren*) e in 
  let eq₁ = (λ { ⟦α⟧ → Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T }) in
  let eq = sym (dep-ext eq₁) in 
  let eq₂ = sym (Tren*-preserves-semantics (Tren*-lift ⟦α⟧ Tren*) T) in
  begin 
    E⟦ Eren _ (Eliftᵣ-l _ ρ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η₁) (extend-tskip γ₁)) ⟦α⟧
  ∎
Eren*-preserves-semantics {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₁ = η₁} {η₂ = η₂} {ρ* = ρ*} {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* (_∙_ {l} {T = T} e T′) = 
  let eq* = Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Tren* Eren* e in 
  let eq*' = Tren*-preserves-semantics {ρ* = ρ*} {η₁ = η₁} {η₂ = η₂} Tren* T′ in 
  let eq = (sym (swap-Tren-[] ρ* T T′)) in 
  let eq' = (sym (Tren*-preserves-semantics Tren* (T [ T′ ]T))) in 
  let eq'''' = λ α → Tren*-preserves-semantics {ρ* = Tliftᵣ ρ* l} {η₁ = α ∷ η₁} {η₂ = α ∷ η₂} (Tren*-lift α Tren*) T in
  let eq'' = (sym (dep-ext eq'''')) in
  let eq''' = sym (Tren*-preserves-semantics {ρ* = Tliftᵣ ρ* l} {η₁ = ⟦ Tren ρ* T′ ⟧ η₂ ∷ η₁} {η₂ = ⟦ Tren ρ* T′ ⟧ η₂ ∷ η₂} (Tren*-lift (⟦ Tren ρ* T′ ⟧ η₂) Tren*) T) in
  let eq₁ = (cong (λ T → ⟦ T ⟧ η₂) eq) in
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tren ρ* T′) (Tren (Tliftᵣ ρ* l) T)) in
  let eq₃ = sym (Tsingle-subst-preserves η₁ T′ T) in
  let eq₄ = cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym eq*') in
  let eq₅ = (cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym (Tren*-preserves-semantics Tren* T′))) in
  begin 
    E⟦ subst (Expr Δ₂ Γ₂) eq (Eren _ ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Eren ρ* ρ e ∙ Tren ρ* T′) ⟩
    subst id eq₁ (E⟦ (Eren ρ* ρ e ∙ Tren ρ* T′) ⟧ η₂ γ₂)
  ≡⟨⟩
    subst id eq₁ (subst id eq₂ (E⟦ (Eren ρ* ρ e) ⟧ η₂ γ₂ (⟦ Tren ρ* T′ ⟧ η₂)))
  ≡⟨ cong (λ e → subst id eq₁ (subst id eq₂ (e (⟦ Tren ρ* T′ ⟧ η₂)))) eq* ⟩
    subst id eq₁ (subst id eq₂ ((subst id eq'' (E⟦ e ⟧ η₁ γ₁)) (⟦ Tren ρ* T′ ⟧ η₂)))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂ x)) 
     (sym (dist-subst′′ (⟦ Tren ρ* T′ ⟧ η₂) (E⟦ e ⟧ η₁ γ₁) eq'' λ α → sym (eq'''' α))) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''' ((E⟦ e ⟧ η₁ γ₁) (⟦ Tren ρ* T′ ⟧ η₂))))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂  (subst id eq''' x))) 
     (dist-subst′′′ (⟦ Tren ρ* T′ ⟧ η₂) (⟦ T′ ⟧ η₁) (E⟦ e ⟧ η₁ γ₁) (Tren*-preserves-semantics Tren* T′) eq₅) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''' (subst id eq₄ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))))
  ≡⟨ subst-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)  
  ∎

-- semantic substituions on expressions


subst-to-env : {σ* : TSub Δ₁ Δ₂} → ESub σ* Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ* η₂)
subst-to-env {η₂ = η₂} {σ* = σ*} σ γ₂ _ T x = subst id (subst-preserves σ* T) (E⟦ σ _ _ x ⟧ η₂ γ₂)

subst-to-env-dist-extend : {T : Type Δ₁ l} {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦e⟧ : ⟦ Tsub σ* T ⟧ η₂)
  → subst-to-env (Eliftₛ {T = T} σ* σ) (extend {Γ = Γ₂} γ₂ ⟦e⟧) ≡ω extend (subst-to-env σ γ₂) (subst id (subst-preserves {η₂ = η₂} σ* T) ⟦e⟧)
subst-to-env-dist-extend {η₂ = η₂} {σ* = σ*} γ₂ σ ⟦e⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  here → refl
  (there {T′ = T′} x) → cong (subst id (subst-preserves {η₂ = η₂} σ* T)) {! (Eren*-preserves-semantics {T = Tsub σ* T} {γ₂ = γ₂} (Tren*-id η₂) (Ewk∈ERen* {T = Tsub σ* T′} γ₂ ⟦e⟧) (σ l T x))  !}

subst-to-env-dist-extend-l : {σ* : TSub Δ₁ Δ₂} 
  → (γ₂ : Env Δ₂ Γ₂ η₂)
  → (σ : ESub σ* Γ₁ Γ₂) 
  → (⟦α⟧ : Set l)
  → subst-to-env (Eliftₛ-l {l = l} σ* σ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₂) ≡ω 
    substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))
subst-to-env-dist-extend-l {η₂ = η₂} {σ* = σ*} γ₂ σ ⟦α⟧ = fun-extω λ l → fun-ext λ T → fun-ext λ where 
  (tskip x) → {!   !}

Esubst-preserves : ∀ {T : Type Δ₁ l} {η₂ : Env* Δ₂} {γ₂ : Env Δ₂ Γ₂ η₂} {σ* : TSub Δ₁ Δ₂} 
  → (σ : ESub σ* Γ₁ Γ₂) (e : Expr Δ₁ Γ₁ T)
  → E⟦ Esub σ* σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ* T)) (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))
Esubst-preserves σ (# n) = refl
Esubst-preserves {l = l} {T = T } {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (` x) =  
  sym (elim-subst id (sym (subst-preserves σ* T)) (subst-preserves σ* T) (E⟦ σ l _ x ⟧ η₂ γ₂))
Esubst-preserves {T = T ⇒ T′} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (ƛ e) = fun-ext λ ⟦e⟧ → 
  let eq* = Esubst-preserves {η₂ = η₂} {γ₂ = extend γ₂ ⟦e⟧} (Eliftₛ σ* σ) e in 
  let eq = sym (subst-preserves {η₂ = η₂} σ* (T ⇒ T′)) in 
  let eq₁ = subst-preserves {η₂ = η₂} σ* T in
  let eq₂ = (sym (subst-preserves {η₂ = η₂} σ* T′)) in
  begin 
    E⟦ Esub σ* (Eliftₛ σ* σ) e ⟧ η₂ (extend γ₂ ⟦e⟧)
  ≡⟨ eq* ⟩
    subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) (subst-to-env (Eliftₛ σ* σ) (extend γ₂ ⟦e⟧)))
  ≡⟨ congωl (λ γ → subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) γ)) (subst-to-env-dist-extend γ₂ σ ⟦e⟧) ⟩
    subst id eq₂ (E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) (subst id eq₁ ⟦e⟧)))
  ≡⟨ dist-subst (λ ⟦e⟧ → E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) ⟦e⟧)) eq₁ eq eq₂ ⟦e⟧ ⟩
    subst id eq (λ ⟦e⟧ → E⟦ e ⟧ (subst-to-env* σ* η₂) (extend (subst-to-env σ γ₂) ⟦e⟧)) ⟦e⟧
  ∎ 
Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_·_ {T = T} {T′ = T′} e₁ e₂) = 
  let eq₁* = Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} σ e₁ in
  let eq₂* = Esubst-preserves {η₂ = η₂} {γ₂ = γ₂} σ e₂ in 
  let eq = sym (subst-preserves {η₂ = η₂} σ* (T ⇒ T′)) in 
  let eq₁ = sym (subst-preserves {η₂ = η₂} σ* T′) in
  let eq₂ = sym (subst-preserves {η₂ = η₂} σ* T) in
  begin 
    E⟦ Esub σ* σ e₁ ⟧ η₂ γ₂ (E⟦ Esub σ* σ e₂ ⟧ η₂ γ₂)
  ≡⟨ cong₂ (λ x y → x y) eq₁* eq₂* ⟩
    (subst id eq (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂))) 
    (subst id eq₂ (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)))
  ≡⟨ dist-subst′ (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)) eq₂ eq eq₁ (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)) ⟩
    subst id eq₁ (E⟦ e₁ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂) (E⟦ e₂ ⟧ (subst-to-env* σ* η₂) (subst-to-env σ γ₂)))
  ∎ 
Esubst-preserves {T = T′} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (Λ_⇒_ l {T = T} e) = fun-ext λ ⟦α⟧ → 
  let eq* = Esubst-preserves {η₂ = ⟦α⟧ ∷ η₂} {γ₂ = extend-tskip γ₂} (Eliftₛ-l σ* σ) e in 
  let eq₁ = (λ { ⟦α⟧ → trans (subst-preserves (Tliftₛ σ* l) T) (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ* ⟦α⟧ η₂)) }) in
  let eq = sym (dep-ext eq₁) in
  let eq′ = sym (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ* l) T) in
  let eq′′ = sym (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tdropₛ (Tliftₛ σ* l)) T′) in
  begin 
    E⟦ Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e ⟧ (⟦α⟧ ∷ η₂) (extend-tskip γ₂)
  ≡⟨ eq* ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) (subst-to-env (Eliftₛ-l σ* σ) (extend-tskip γ₂)))
  ≡⟨ congωl (λ γ → subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) γ)) (subst-to-env-dist-extend-l γ₂ σ ⟦α⟧) ⟩
    subst id eq′ (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* (Twkₛ σ*) (⟦α⟧ ∷ η₂)) 
      (substωω (Env _ _) (congωω (⟦α⟧ ∷_) (symω (subst-to-env*-wk σ* ⟦α⟧ η₂))) (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ₂))))
  ≡⟨ {!   !} ⟩
    {!   !}
  ≡⟨ {! cong  !} ⟩
    subst id (sym (eq₁ ⟦α⟧)) (E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂)))
  ≡⟨ dist-subst′′ ⟦α⟧ (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) eq (λ ⟦α⟧ → sym (eq₁ ⟦α⟧)) ⟩
    subst id eq (λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ subst-to-env* σ* η₂) (extend-tskip (subst-to-env σ γ₂))) ⟦α⟧
  ∎ 
Esubst-preserves {Δ₂ = Δ₂} {Γ₂ = Γ₂} {η₂ = η₂} {γ₂ = γ₂} {σ* = σ*} σ (_∙_ {l} {T = T} e T′) = 
  let η₁ = (subst-to-env* σ* η₂) in
  let γ₁ = (subst-to-env σ γ₂) in
  let eq* = Esubst-preserves {γ₂ = γ₂} σ e in 
  let eq*' = subst-preserves {η₂ = η₂} σ* T′ in 
  let eq = (sym (swap-Tsub-[] σ* T T′)) in 
  let eq' = (sym (subst-preserves {η₂ = η₂} σ* (T [ T′ ]T))) in  
  let eq'''' = λ α → trans (subst-preserves {η₂ = α ∷ η₂} (Tliftₛ σ* l) T) (congωl (λ η → ⟦ T ⟧ (α ∷ η)) (subst-to-env*-wk σ* α η₂)) in
  let eq''''′ = λ α → trans (congωl (λ η → ⟦ T ⟧ (α ∷ η)) (symω (subst-to-env*-wk σ* α η₂))) (sym (subst-preserves (Tliftₛ σ* l) T)) in
  let eq'' = (sym (dep-ext eq'''')) in
  let eq''' = sym (subst-preserves {η₂ = ⟦ Tsub σ* T′ ⟧ η₂ ∷ η₂} (Tliftₛ σ* l) T) in
  let eq''''' = trans (congωl (λ η → ⟦ T ⟧ (⟦ Tsub σ* T′ ⟧ η₂ ∷ η)) (symω (subst-to-env*-wk σ* (⟦ Tsub σ* T′ ⟧ η₂) η₂))) eq''' in
  let eq₁ = (cong (λ T → ⟦ T ⟧ η₂) eq) in
  let eq₂ = sym (Tsingle-subst-preserves η₂ (Tsub σ* T′) (Tsub (Tliftₛ σ* l) T)) in
  let eq₃ = (sym (Tsingle-subst-preserves η₁ T′ T)) in 
  let eq₄ = cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym eq*') in
  let eq₅ = (cong (λ x → ⟦ T ⟧ (x ∷ η₁)) (sym (subst-preserves {η₂ = η₂} σ* T′))) in
  begin 
    E⟦ subst (Expr Δ₂ Γ₂) eq (Esub σ* σ e ∙ Tsub σ* T′) ⟧ η₂ γ₂
  ≡⟨ dist-subst' {F = Expr Δ₂ Γ₂} {G = id} (λ T → ⟦ T ⟧ η₂) (λ e → E⟦ e ⟧ η₂ γ₂) eq eq₁ (Esub σ* σ e ∙ Tsub σ* T′) ⟩
    subst id eq₁ (subst id eq₂ (E⟦ Esub σ* σ e ⟧ η₂ γ₂ (⟦ Tsub σ* T′ ⟧ η₂)))
  ≡⟨ cong (λ e → subst id eq₁ (subst id eq₂ (e (⟦ Tsub σ* T′ ⟧ η₂)))) eq* ⟩
    subst id eq₁ (subst id eq₂ ((subst id eq'' (E⟦ e ⟧ η₁ γ₁)) (⟦ Tsub σ* T′ ⟧ η₂)))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂ x)) 
     (sym (dist-subst′′ (⟦ Tsub σ* T′ ⟧ η₂) (E⟦ e ⟧ η₁ γ₁) eq'' eq''''′)) ⟩ 
    subst id eq₁ (subst id eq₂  (subst id eq''''' ((E⟦ e ⟧ η₁ γ₁) (⟦ Tsub σ* T′ ⟧ η₂))))
  ≡⟨ cong (λ x → subst id eq₁ (subst id eq₂  (subst id eq''''' x))) 
     (dist-subst′′′ (⟦ Tsub σ* T′ ⟧ η₂) (⟦ T′ ⟧ η₁) (E⟦ e ⟧ η₁ γ₁) (subst-preserves σ* T′) eq₅) ⟩
    subst id eq₁ (subst id eq₂  (subst id eq''''' (subst id eq₄ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))))
  ≡⟨ subst-elim′′′ ((E⟦ e ⟧ η₁ γ₁) (⟦ T′ ⟧ η₁)) eq₁ eq₂ eq''''' eq₄ eq' eq₃ ⟩
    subst id eq' (subst id eq₃ (E⟦ e ⟧ η₁ γ₁ (⟦ T′ ⟧ η₁)))
  ≡⟨⟩
    subst id eq' (E⟦ e ∙ T′ ⟧ η₁ γ₁)
  ∎         
   
