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

-- need to generalize to general type substitution

LRVsubst : ∀ {Δ}{l}{l′}
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
LRVsubst Γ ρ T′ R′ (` x) v z lrv-t = {! !}
LRVsubst Γ ρ T′ R′ (T₁ ⇒ T₂) v z lrv-t = {!!}
LRVsubst Γ ρ T′ R′ (`∀α l , T) v z lrv-t = {! !}
LRVsubst Γ ρ T′ R′ `ℕ v z (n , v≡#n , n≡z) =
  n ,
  trans (subst-id Value (ext-σ-T′≡σ[T′] T′ `ℕ ρ R′)) v≡#n ,
  trans n≡z (trans (subst-∘ {P = id} {f = λ ⟦T′⟧ → ℕ} (sym (subst-preserves (subst←RE ρ) T′)))
                   (subst-irrelevant (cong (λ ⟦T′⟧ → ℕ) (sym (subst-preserves (subst←RE ρ) T′)))
                                     (sym (Tsingle-subst-preserves (subst-to-env* (subst←RE ρ) []) T′ `ℕ)) z))
