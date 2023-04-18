# Imports

```
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.List using (List; []; _∷_; _++_)
infix 25 _▷_
pattern _▷_ xs x = x ∷ xs
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
```

# Sorts

```
data Bindable : Set where 
  bind    : Bindable
  no-bind : Bindable

data Sort : Bindable → Set where
  eₛ : Sort bind
  τₛ : Sort bind
  κₛ : Sort no-bind

Bind : Set
Bind = Sort bind

Scope : Set
Scope = List (Sort bind)

variable 
  b b' b'' b₁ b₂ b₃ : Bindable
  s s' s'' s₁ s₂ s₃ : Sort b
  S S' S'' S₁ S₂ S₃ : Scope
  x x' x'' x₁ x₂ x₃ : eₛ ∈ S
  α α' α'' α₁ α₂ α₃ : τₛ ∈ S
```

# Syntax

```
infixr 3 _⊢_∶_ _↪_ _⊢*_∶_
infixr 4 ∀α_  ƛ[_]_
infixr 5 _⇒_
infixl 5 _·[_]_ 
infix  5 _→ₛ_ _→ᵣ_
infixl 6 _↑_
infix  7 `_

data Term : Scope → Sort b → Set where
  `_     : s ∈ S → Term S s
  ƛ[_]_  : (s : Bind) → Term (S ▷ s) eₛ → Term S eₛ
  _·[_]_ : Term S eₛ → (s : Bind) → Term S s → Term S eₛ
  _⇒_    : Term S τₛ → Term S τₛ → Term S τₛ
  ∀α_    : Term (S ▷ τₛ) τₛ → Term S τₛ
  ⋆      : Term S κₛ

Var : Scope → Sort bind → Set
Var S s = s ∈ S

variable 
  v v' v'' v₁ v₂ v₃ : Var S s
  t t' t'' t₁ t₂ t₃ : Term S s
  e e' e'' e₁ e₂ e₃ : Term S eₛ
  τ τ' τ'' τ₁ τ₂ τ₃ : Term S τₛ
```

# Renaming & Substitution

```
record Kit : Set₁ where
  constructor kit 
  field
    Elem  : Scope → Bind → Set
    ↑ⱽ    : ∀ s → Var S s  → Elem S s
    ↓ᵀ    : ∀ s → Elem S s → Term S s
    wk    : ∀ s → Elem S s → Elem (S ▷ s') s
    ≡↑ᵀ↓ⱽ : ∀ (x : Var S s) → ↓ᵀ _ (↑ⱽ _ x) ≡ ` x
    ≡wk   : ∀ s' (x : Var S s) → wk {s' = s'} _ (↑ⱽ _ x) ≡ ↑ⱽ _ (there x)

  _-→_ : Scope → Scope → Set
  _-→_ S₁ S₂ = ∀ s → Var S₁ s → Elem S₂ s

open Kit {{...}}

_-[_]→_ : Scope → (K : Kit) → Scope → Set
S₁ -[ K ]→ S₂ = Kit._-→_ K S₁ S₂

_↑_ : {{K : Kit}} → S₁ -[ K ]→ S₂ → (s : Bind) → (S₁ ▷ s) -[ K ]→ (S₂ ▷ s)
(K ↑ s) _ (here refl)  = ↑ⱽ _ (here refl)
(K ↑ s) _ (there x) = wk _ (K _ x)

_⋯_ : {{K : Kit}} → Term S₁ s → S₁ -[ K ]→ S₂ → Term S₂ s 
_⋯_ {s = s} (` x) K = ↓ᵀ s (K s x)
(ƛ[ s ] t) ⋯ K = ƛ[ s ] (t ⋯ (K ↑ s))
(t₁ ·[ s ] t₂) ⋯ K = (t₁ ⋯ K) ·[ s ] (t₂ ⋯ K)
(τ₁ ⇒ τ₂) ⋯ K = (τ₁ ⋯ K) ⇒ (τ₂ ⋯ K)
(∀α τ) ⋯ K = ∀α (τ ⋯ (K ↑ τₛ))
⋆ ⋯ K = ⋆

instance kitᵣ : Kit
Kit.Elem  kitᵣ     = Var
Kit.↑ⱽ    kitᵣ _   = id
Kit.↓ᵀ    kitᵣ _   = `_
Kit.wk    kitᵣ _   = there
Kit.≡wk   kitᵣ _ _ = refl
Kit.≡↑ᵀ↓ⱽ kitᵣ _ = refl
 
instance kitₛ : Kit
Kit.Elem  kitₛ     = Term
Kit.↑ⱽ    kitₛ _   = `_
Kit.↓ᵀ    kitₛ _   = id
Kit.wk    kitₛ _   = _⋯ wk
Kit.≡wk   kitₛ _ _ = refl
Kit.≡↑ᵀ↓ⱽ kitₛ _ = refl

_→ᵣ_ : Scope → Scope → Set
_→ᵣ_ = _-[ kitᵣ ]→_

_→ₛ_ : Scope → Scope → Set
_→ₛ_ = _-[ kitₛ ]→_

idₖ : {{K : Kit}} → S -[ K ]→ S
idₖ {{K}} = Kit.↑ⱽ K

liftₖ : {{K : Kit}} → S₁ -[ K ]→ S₂ → Elem S₂ s → (S₁ ▷ s) -[ K ]→ S₂
liftₖ K t _ (here refl) = t
liftₖ K _ _ (there x)   = K _ x

[_] : Term S s → (S ▷ s) →ₛ S
[_] = liftₖ idₖ
```

# Context

```
bind-of : Bind → Bindable 
bind-of eₛ = bind
bind-of τₛ = no-bind

type-of : (s : Bind) → Sort (bind-of s)
type-of eₛ = τₛ
type-of τₛ = κₛ 

variable 
  T T' T'' T₁ T₂ T₃ : Term S (type-of s)

data Ctx : Scope → Set where
  ∅   : Ctx []
  _▶_ : Ctx S → Term S (type-of s) → Ctx (S ▷ s)

lookup : Ctx S → Var S s → Term S (type-of s) 
lookup {s = eₛ} (Γ ▶ T) (here refl) = wk _ T
lookup {s = eₛ} (Γ ▶ T) (there x) = wk _ (lookup Γ x)
lookup {s = τₛ} (Γ ▶ T) x = ⋆

variable 
  Γ Γ' Γ'' Γ₁ Γ₂ Γ₃ : Ctx S
```

# Typing

```
data _⊢_∶_ : Ctx S → Term S s → Term S (type-of s) → Set where
  ⊢x :  
    lookup Γ x ≡ τ →
    Γ ⊢ ` x ∶ τ
  ⊢λ : ∀ {Γ : Ctx S} →
    Γ ▶ τ ⊢ e ∶ wk τₛ τ' →  
    Γ ⊢ ƛ[ eₛ ] e ∶ τ ⇒ τ' 
  ⊢Λ : 
    Γ ▶ ⋆ ⊢ e ∶ τ →  
    Γ ⊢ ƛ[ τₛ ] e ∶ ∀α τ
  ⊢· : 
    Γ ⊢ e₁ ∶ τ₁ ⇒ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    Γ ⊢ e₁ ·[ eₛ ] e₂ ∶ τ₂
  ⊢• : ∀ {Γ : Ctx S} →
    Γ ⊢ e ∶ ∀α τ →
    Γ ⊢ e ·[ τₛ ] τ' ∶ τ ⋯ [ τ' ]
  ⊢τ : 
    Γ ⊢ τ ∶ ⋆

_⊢*_∶_ : Ctx S₂ → S₁ →ₛ S₂ → Ctx S₁ → Set
_⊢*_∶_ {S₁ = S₁} Γ₂ σ Γ₁ = ∀ {s₁} → (x : Var S₁ s₁) → Γ₂ ⊢ σ _ x ∶ (lookup Γ₁ x ⋯ σ)
```  

# Semantics

```
data Val : Term S s → Set where
  v-ƛ : Val (ƛ[ s ] e)
  v-τ : Val τ

data _↪_ : Term S eₛ → Term S eₛ → Set where
  β-ƛ  : ∀ {t₂ : Term S s} →
    Val t₂ →
    (ƛ[ s ] e₁) ·[ s ] t₂ ↪ (e₁ ⋯ [ t₂ ])
  ξ-·₁ : ∀ {t₂ : Term S s} →
    e₁ ↪ e →
    e₁ ·[ s ] t₂ ↪ e ·[ s ] t₂
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    e₁ ·[ eₛ ] e₂ ↪ e₁ ·[ eₛ ] e 
```

# Soundness

## Progress

```
progress : 
  ∅ ⊢ e ∶ τ →
  (∃[ e' ] (e ↪ e')) ⊎ Val e
progress (⊢λ t) = inj₂ v-ƛ
progress (⊢Λ t) = inj₂ v-ƛ
progress (⊢· ⊢e₁ ⊢e₂ ) with progress ⊢e₁ | progress ⊢e₂ 
... | inj₁ (_ , e₁↪e) | _ = inj₁ (_ , ξ-·₁ e₁↪e)
... | inj₂ v | inj₁ (_ , e₂↪e) = inj₁ (_ , ξ-·₂ e₂↪e v)
... | inj₂ (v-ƛ {eₛ}) | inj₂ v = inj₁ (_ , β-ƛ v)
progress (⊢• ⊢e) with progress ⊢e 
... | inj₁ (e' , e↪e') = inj₁ (_ , ξ-·₁ e↪e')
... | inj₂ (v-ƛ {τₛ}) = inj₁ (_ , β-ƛ v-τ)
```

## Subject Reduction

``` 
variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C      : Set ℓ
  
postulate
  fun-ext : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} →
    (∀ (x : A) → f x ≡ g x) →
    f ≡ g

fun-ext₂ : ∀ {A₁ : Set ℓ₁} {A₂ : A₁ → Set ℓ₂} {B : (x : A₁) → A₂ x → Set ℓ₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

id↑≡id : ∀ {{K : Kit}} S s →
  idₖ {{K}} ↑ s ≡ idₖ {S = S ▷ s} {{K}}
id↑≡id S s = fun-ext₂ λ where
  _ (here refl) → refl
  _ (there x)   → ≡wk s x

⋯id : ∀ {{K : Kit}} (t : Term S s) →
  t ⋯ idₖ {{K}} ≡ t
⋯id (` x) = ≡↑ᵀ↓ⱽ x
⋯id {S} {{K}} (ƛ[ s ] t) rewrite id↑≡id {{K}} S s = cong ƛ[ s ]_ (⋯id t)
⋯id (e ·[ s ] t) = cong₂ _·[ s ]_ (⋯id e) (⋯id t)
⋯id (τ₁ ⇒ τ₂) = cong₂ _⇒_ (⋯id τ₁) (⋯id τ₂)
⋯id {S} {{K}} (∀α τ) rewrite id↑≡id {{K}} S τₛ = cong ∀α_ (⋯id τ)
⋯id ⋆ = refl

⊢σ-preserves : ∀ {σ : S₁ →ₛ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
                 {t : Term S₁ s} {T : Term S₁ (type-of s)} →
  Γ₂ ⊢* σ ∶ Γ₁ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ t ⋯ σ ∶ T ⋯ σ
⊢σ-preserves ⊢σ ⊢e = {!   !}

subject-reduction : ∀ {Γ : Ctx S} →
  Γ ⊢ e ∶ τ →
  e ↪ e' →
  Γ ⊢ e' ∶ τ
subject-reduction {τ = τ} (⊢· e₁ e₂) (β-ƛ v) rewrite ⋯id {{K = kitₛ}} τ = ⊢σ-preserves {!   !} {!   !}
subject-reduction (⊢· e₁ e₂) (ξ-·₁ e₁↪e) = ⊢· (subject-reduction e₁ e₁↪e) e₂
subject-reduction (⊢· t t₁) (ξ-·₂ e₂↪e x) = ⊢· t (subject-reduction t₁ e₂↪e)
subject-reduction (⊢• e) (β-ƛ v) = {!   !}
subject-reduction (⊢• e) (ξ-·₁ e↪e') = ⊢• (subject-reduction e e↪e')
```  