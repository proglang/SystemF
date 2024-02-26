-- This file is only used to generate examples for the paper, and is
-- not part of the actual formalization.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; module ≡-Reasoning)

--! SubstExamples >

--! Def
subst : ∀ {ℓ ℓ′} {A : Set ℓ} {x y : A} (P : A → Set ℓ′) → x ≡ y → P x → P y
subst P refl Px = Px

module Vec where
  open import Data.Nat using (ℕ; suc; zero; _+_)
  open import Data.Nat.Properties using (+-comm; +-assoc)

    --! DistSubst
  dist-subst :
    ∀ {ℓ ℓ' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A}
      {F : A → Set ℓ₁} {G : B → Set ℓ₂}
    → (a→b : A → B)
    → (f : ∀ {a} → F a → G (a→b a))
    → (a₁≡a₂ : a₁ ≡ a₂)
    → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
    → (x : F a₁) 
    → f {a₂} (subst F a₁≡a₂ x) ≡ subst G b₁≡b₂ (f {a₁} x)
  dist-subst _ _ refl refl _ = refl

  --! Vec
  data Vec (A : Set) : ℕ → Set where
    []   : Vec A zero
    _∷_  : ∀ {n} → A → Vec A n → Vec A (suc n)

  --! Append
  _++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
  []        ++ ys = ys
  (x ∷ xs)  ++ ys = x ∷ (xs ++ ys)

  --! AppendR
  _++ʳ_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (n + m)
  _++ʳ_ {A} {m} {n} xs ys = subst (λ ■ → Vec A ■) (+-comm m n) (xs ++ ys)

  module HomEq where

    open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
    open ≡-Reasoning

    -- ++-assoc : ∀ {A m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p) →
    --   (xs ++ ys) ++ zs ≡ subst (Vec A) (sym (+-assoc m n p)) (xs ++ (ys ++ zs))
    -- ++-assoc {A} {.0}     {n} {p} []        ys zs = refl
    -- ++-assoc {A} {suc m}  {n} {p} (x ∷ xs)  ys zs =
    --   let F = Vec A ; E₁ = sym (+-assoc m n p) ; E₂ = sym (+-assoc (suc m) n p) in
    --   ((x ∷ xs) ++ ys) ++ zs               ≡⟨ refl ⟩
    --   x ∷ ((xs ++ ys) ++ zs)               ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    --   x ∷ subst F E₁ (xs ++ (ys ++ zs))    ≡⟨ {!!} ⟩
    --   subst F E₂ (x ∷ (xs ++ (ys ++ zs)))  ∎

    --! Assoc
    ++-assoc : ∀ {A m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p) →
      (xs ++ ys) ++ zs ≡ subst (Vec A) (sym (+-assoc m n p)) (xs ++ (ys ++ zs))
    ++-assoc {A} {.0}     {n} {p} []        ys zs = refl
    ++-assoc {A} {suc m}  {n} {p} (x ∷ xs)  ys zs =
      let F = Vec A ; E₁ = sym (+-assoc m n p) ; E₂ = sym (+-assoc (suc m) n p) in
      ((x ∷ xs) ++ ys) ++ zs               ≡⟨ refl ⟩
      x ∷ ((xs ++ ys) ++ zs)               ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
      x ∷ subst F E₁ (xs ++ (ys ++ zs))    ≡⟨ dist-subst suc (x ∷_) E₁ E₂ ((xs ++ (ys ++ zs))) ⟩
      subst F E₂ (x ∷ (xs ++ (ys ++ zs)))  ∎

    --! AssocR
    ++ʳ-assoc : ∀ {A m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p) →
      (xs ++ʳ ys) ++ʳ zs ≡ subst (Vec A) (+-assoc p n m) (xs ++ʳ (ys ++ʳ zs))
    ++ʳ-assoc {A} {.0} {n} {p} [] ys zs =
      let  F = Vec A ;           E₁ = +-comm (n + 0) p ;  E₂ = +-comm 0 n
           E₃ = +-assoc p n 0 ;  E₄ = +-comm 0 (p + n) ;  E₅ = +-comm n p in
      (([] ++ʳ ys) ++ʳ zs)                             ≡⟨ refl ⟩
      subst F E₁ (subst F E₂ ys ++ zs)                 ≡⟨ {!!} ⟩
      subst F E₃ (subst F E₄ (subst F E₅ (ys ++ zs)))  ≡⟨ refl ⟩
      subst F E₃ ([] ++ʳ (ys ++ʳ zs))                  ∎

    ++ʳ-assoc {A} {suc m} {n} {p} (x ∷ xs) ys zs =
      begin
        (((x ∷ xs) ++ʳ ys) ++ʳ zs)
      ≡⟨ refl ⟩
        {!!}
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ refl ⟩
        subst (Vec A) (+-assoc p n (suc m)) ((x ∷ xs) ++ʳ (ys ++ʳ zs))
      ∎

  module HetEq where
    open import Relation.Binary.HeterogeneousEquality
      using (_≅_; refl; sym; trans; cong; cong₂; module ≅-Reasoning; ≡-to-≅)
    open ≅-Reasoning

    --! SubstRemovable
    ≡-subst-removable : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y} (eq : x ≡ y) (z : P x) →
                        subst P eq z ≅ z
    ≡-subst-removable P refl z = refl

    --! AssocHet
    ++-assoc : ∀ {A m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p) →
      (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
    ++-assoc {A} {.0}     {n} {p} []        ys zs = refl
    ++-assoc {A} {suc m}  {n} {p} (x ∷ xs)  ys zs = begin
      ((x ∷ xs) ++ ys) ++ zs  ≅⟨ refl ⟩
      x ∷ ((xs ++ ys) ++ zs)  ≅⟨ cong₂ {A = ℕ} {B = λ a → Vec A a} (λ a b → x ∷ b)
                                  (≡-to-≅ (+-assoc m n p)) (++-assoc xs ys zs) ⟩
      x ∷ (xs ++ (ys ++ zs))  ≅⟨ refl ⟩
      (x ∷ xs) ++ (ys ++ zs)  ∎

    --! AssocRHet
    ++ʳ-assoc : ∀ {A m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p) →
      (xs ++ʳ ys) ++ʳ zs ≅ xs ++ʳ (ys ++ʳ zs)
    ++ʳ-assoc {A} {.0} {n} {p} [] ys zs = begin
      let  F = Vec A ;           E₁ = +-comm (n + 0) p ;  E₂ = +-comm 0 n
           E₃ = +-assoc p n 0 ;  E₄ = +-comm 0 (p + n) ;  E₅ = +-comm n p in
      (([] ++ʳ ys) ++ʳ zs)                ≅⟨ refl ⟩
      subst F E₁ (subst F E₂ ys ++ zs)    ≅⟨ ≡-subst-removable F E₁ _ ⟩
      subst F E₂ ys ++ zs                 ≅⟨ cong₂ {B = Vec A} (λ a b → b ++ zs)
                                              (sym (≡-to-≅ E₂)) (≡-subst-removable F E₂ _) ⟩
      ys ++ zs                            ≅⟨ sym (≡-subst-removable F E₅ _) ⟩
      subst F E₅ (ys ++ zs)               ≅⟨ sym (≡-subst-removable F E₄ _) ⟩
      subst F E₄ (subst F E₅ (ys ++ zs))  ≅⟨ refl ⟩
      [] ++ʳ (ys ++ʳ zs)                  ∎

    ++ʳ-assoc {A} {suc m} {n} {p} (x ∷ xs) ys zs =
      {!!}

  module OnlyType where

    open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
    open ≡-Reasoning

    --! AssocType
    ++-assoc : ∀ {A m n p} (xs : Vec A m) (ys : Vec A n) (zs : Vec A p) →
      (xs ++ ys) ++ zs ≡ subst (Vec A) (sym (+-assoc m n p)) (xs ++ (ys ++ zs))

    ++-assoc xs ys zs = {!(xs ++ ys) ++ zs!}

open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open ≡-Reasoning
open import Types
open import TypeSubstitution hiding (_∘ₛₛ_)
open import TypeSubstProperties hiding (fusion-Tsub-Tsub)
open import Expressions
open import ExprSubstitution hiding (Eidₛ; ESub)

--! ESubDef
ESub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ESub {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ* Γ₁ Γ₂ = ∀ l (T : Type Δ₁ l) → inn T Γ₁ → Expr Δ₂ Γ₂ (Tsub σ* T)

--! EidDef
Eidₛ : ESub Tidₛ Γ Γ
Eidₛ _ T x = subst (Expr _ _) (sym (TidₛT≡T T)) (` x)

--! EidNeutral
Eidₛe≡e : ∀ (e : Expr Δ Γ T) → Esub Tidₛ Eidₛ e ≡ subst (Expr Δ Γ) (sym (TidₛT≡T _)) e
Eidₛe≡e {Δ = Δ} {Γ = Γ} (`suc e) =
  Esub Tidₛ Eidₛ (`suc e)                       ≡⟨ refl ⟩
  `suc (Esub Tidₛ Eidₛ e)                       ≡⟨ cong `suc (Eidₛe≡e e) ⟩
  `suc (subst (Expr Δ Γ) (sym (TidₛT≡T `ℕ)) e)  ≡⟨ {!!} ⟩
  subst (Expr Δ Γ) (sym (TidₛT≡T `ℕ)) (`suc e)  ∎

Eidₛe≡e = {!!}

--! TCompSS
_∘Tₛₛ_ : TSub Δ₂ Δ₃ → TSub Δ₁ Δ₂ → TSub Δ₁ Δ₃
(σ₁ ∘Tₛₛ σ₂) _ x = Tsub σ₁ (σ₂ _ x)


--! FusionTSubTSub
fusion-Tsub-Tsub : ∀ (T : Type Δ₁ l) (σ₁ : TSub Δ₂ Δ₃) (σ₂ : TSub Δ₁ Δ₂) →
  Tsub σ₁ (Tsub σ₂ T) ≡ Tsub (σ₁ ∘Tₛₛ σ₂) T

fusion-Tsub-Tsub = {!!}

--! ECompSS
_∘Eₛₛ_ : ∀ {σ₁* : TSub Δ₂ Δ₃} {σ₂* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
  → ESub σ₁* Γ₂ Γ₃ → ESub σ₂* Γ₁ Γ₂ → ESub (σ₁* ∘Tₛₛ σ₂*) Γ₁ Γ₃
_∘Eₛₛ_ {Δ₃ = Δ₃} {σ₁* = σ₁*} {σ₂* = σ₂*} {Γ₃ = Γ₃} σ₁ σ₂ l T x =
  subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tsub T σ₁* σ₂*) (Esub _ σ₁ (σ₂ _ _ x))

--! FusionESubESub
fusion-Esub-Esub : 
  ∀ {σ₁* : TSub Δ₂ Δ₃} {σ₂* : TSub Δ₁ Δ₂}
    {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    {T : Type Δ₁ l}
    (e : Expr Δ₁ Γ₁ T)
    (σ₂ : ESub σ₂* Γ₁ Γ₂) (σ₁ : ESub σ₁* Γ₂ Γ₃)  →
  let sub = subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tsub T σ₁* σ₂*) in
  sub (Esub σ₁* σ₁ (Esub σ₂* σ₂ e)) ≡ Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) e

fusion-Esub-Esub {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} e σ ρ =
  {!!}
