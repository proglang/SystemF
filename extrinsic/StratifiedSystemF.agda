module StratifiedSystemF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open ≡-Reasoning

open import Kits

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀α_ letrec_；_ trait[o∶_]_ impl[_∶_]_；_ ƛ[_]_ [_]⇒_
infixr  6  _⇒_ _↓_ _∶_ 
infixl  6  _·_  
infix   6 _∙ _•
infix   7  `_ Maybe_ some_ ref_ ζ_

-- Sorts -----------------------------------------------------------------------

data TySort : Set where
  m : TySort
  p : TySort

data Sort : SortTy → Set where
  𝕖     : ℕ → Sort Var
  𝕥     : TySort → ℕ → Sort Var
  𝕔     : ℕ → Sort Var
  𝕜     : Sort NoVar

-- Syntax ----------------------------------------------------------------------

private variable
  st st₁ st₂ st₃ st' st₁' st₂' : SortTy
  ts ts₁ ts₂ ts₃ ts' ts₁' ts₂' : TySort
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : List (Sort Var)
  x y z x₁ x₂                : S ∋ s
  n n₁ n₂                    : ℕ

-- impls for functions, what is the function type? 
-- -> see Maybe (α → α), what do we apply the Λα. to? 
-- -> type substiution in the semantic neccessary with the function type, which we dont know without type inference of the argument applyed
--  solution 1: type semantics
--  solution 2: type inference in semantics
--  solution 3: erase type information from expressions

-- impl block depend on other impl blocks, does not work with substiution
-- -> stores
-- -> how do we translate these stores with lists of impl blocks?
-- trait eq : ∀α. α → α → Bool in 
-- impl eq : Bool → Bool → Bool ...
-- impl eq : ∀α. [eq : α → α → Bool] => Maybe α → Maybe α → Bool
--   Λα. λx. → Λβ. ƛ(eq : α → α → Bool). λx. λy. ...
-- impl eq : ∀α. [eq : α → α → Bool] => ∀β. [eq : β → β → Bool] => (α, β) → (α, β) → Bool
 

-- eq Bool true false
-- eq (Maybe Bool) (some true) (some false)
-- -> eq_mb Bool (some true) (some false)
-- eq (Bool, Bool) (true, true) (true, true)
-- -> eq_pr Bool ∎ Bool ∎ (true, true) (true, true)

data _⊢_ : List (Sort Var) → Sort st → Set where
  -- System F
  `_              : S ∋ s → S ⊢ s                
  λx_             : (𝕖 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n          
  Λα_             : (𝕥 m n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n 
  ∀α_             : (𝕥 m n ∷ S) ⊢ 𝕥 ts n → S ⊢ 𝕥 p n 
  ζ_              : S ⊢ 𝕥 ts n → S ⊢ 𝕥 m n -- do not use in language! neccessary for translation from constraints in system o to higher order functions in system f 
                                           -- we could also add a third index to the type sort that indicates the use of forbidden "zeta lifting" (i.e. using system f types)
  _·_             : S ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n
  _∙              : S ⊢ 𝕖 n → S ⊢ 𝕖 n 
  _⇒_             : S ⊢ 𝕥 m n → S ⊢ 𝕥 m n → S ⊢ 𝕥 m n
  letrec_；_      : (𝕖 n ∷ S) ⊢ 𝕖 n → (𝕖 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n
  ★               : S ⊢ 𝕜
  -- Overloading
  trait[o∶_]_     : S ⊢ 𝕥 ts n → S ⊢ 𝕖 (suc n) → S ⊢ 𝕖 n -- rust would allow S ⊢ t ts (suc n), so maybe we should too?
  impl[_∶_]_；_   : Fin n → S ⊢ 𝕥 ts n → S ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n  
  ref_            : Fin n → S ⊢ 𝕖 n  
  
  -- Constraints 
  _∶_             : Fin n → S ⊢ 𝕥 m n → S ⊢ 𝕔 n
  ƛ[_]_           : S ⊢ 𝕔 n → (𝕔 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n  
  _•              : S ⊢ 𝕖 n → S ⊢ 𝕖 n 
  [_]⇒_           : S ⊢ 𝕔 n → S ⊢ 𝕥 ts n → S ⊢ 𝕥 p n
  -- Exemplary expressions & types
  true            : S ⊢ 𝕖 n 
  false           : S ⊢ 𝕖 n
  _↓_             : S ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n -- {nor} is a complete operator set for propositional logic 
  Bool            : S ⊢ 𝕥 m n
  none            : S ⊢ 𝕖 n
  some_           : S ⊢ 𝕖 n → S ⊢ 𝕖 n
  case_[x→_；_]   : S ⊢ 𝕖 n → (𝕖 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n
  Maybe_          : S ⊢ 𝕥 m n → S ⊢ 𝕥 m n

-- example program with overloading: 
_ : [] ⊢ 𝕖 zero
_ = trait[o∶ ∀α ` zero ⇒ ` zero ⇒ Bool ] 
    impl[ zero ∶ Bool ⇒ Bool ⇒ Bool ] λx λx (` zero ↓ ` zero) ↓ (` (suc zero) ↓ ` (suc zero)) ； 
    impl[ zero ∶ ∀α [ zero ∶ ` zero ⇒ ` zero ⇒ Bool ]⇒ Maybe ` zero ⇒ Maybe ` zero ⇒ Bool ] 
        Λα ƛ[ zero ∶ ` zero ⇒ ` zero ⇒ Bool ] λx λx 
          case `  (suc zero) [x→ case ` (suc zero) [x→ ref zero · ` zero · ` (suc zero) ； false ] ； 
                             case ` zero [x→ false ； true ] ] ； 
    ref zero · some true · some true
--  (Λα ƛ[ zero ∶ ` zero ⇒ ` zero ⇒ Bool ] λx λx ..) ∙ • · some true · some true

-- .. and its translation:
_ : [] ⊢ 𝕖 zero
_ = letrec λx λx (` zero ↓ ` zero) ↓ (` (suc zero) ↓ ` (suc zero)) ； 
    letrec Λα λx λx λx 
          case `  (suc zero) [x→ case ` (suc zero) [x→ ` (suc (suc (suc (suc zero)))) · ` zero · ` (suc zero) ； false ] ； 
                             case ` zero [x→ false ； true ] ] ； 
    ` zero ∙ · ` (suc zero) · some true · some true

private variable
  e e₁ e₂ e₃ e' e₁' e₂'  : S ⊢ 𝕖 n
  t t₁ t₂ t₃ t' t₁' t₂'  : S ⊢ 𝕥 ts n
  c c₁ c₂ c₃ c' c₁' c₂'  : S ⊢ 𝕔 n
  k k₁ k₂ k₃ k' k₁' k₂'  : S ⊢ 𝕜
  E E₁ E₂ E₃ E' E₁' E₂'  : S ⊢ s


-- Substitution & Lemmas -------------------------------------------------------

-- Can be derived in the full framework.
SystemF-Syntax : Syntax
SystemF-Syntax = record
  { Sort         = Sort
  ; _⊢_          = _⊢_
  ; `_           = `_
  ; `-injective  = λ { refl → refl } }

open Syntax SystemF-Syntax hiding (Sort; _⊢_; `_)

-- Can be derived in the full framework.
_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)                    ⋯ ϕ = `/id (x & ϕ)
(λx e)                   ⋯ ϕ = λx e ⋯ (ϕ ↑ _)
(Λα e)                   ⋯ ϕ = Λα e ⋯ (ϕ ↑ _)
(∀α t)                   ⋯ ϕ = ∀α t ⋯ (ϕ ↑ _)
(ζ t)                    ⋯ ϕ = ζ t ⋯ ϕ
(e₁ · e₂)                ⋯ ϕ = e₁ ⋯ ϕ · e₂ ⋯ ϕ
(e ∙)                    ⋯ ϕ = e ⋯ ϕ ∙
(t₁ ⇒ t₂)                ⋯ ϕ = t₁ ⋯ ϕ ⇒ t₂ ⋯ ϕ
(letrec e₂ ； e₁)        ⋯ ϕ = letrec e₂ ⋯ (ϕ ↑ _) ； e₁ ⋯ (ϕ ↑ _)
★                        ⋯ ϕ = ★
(trait[o∶ t ] e)         ⋯ ϕ = trait[o∶ t ⋯ ϕ ] e ⋯ ϕ
(impl[ o ∶ t ] e₁ ； e₂) ⋯ ϕ = impl[ o ∶ t ⋯ ϕ ] e₁ ⋯ ϕ ； e₂ ⋯ ϕ
(ref o)                  ⋯ ϕ = ref o
(o ∶ t)                  ⋯ ϕ = o ∶ t ⋯ ϕ
(ƛ[ c ] e)               ⋯ ϕ = ƛ[ c ⋯ ϕ ] e ⋯ (ϕ ↑ _)
(e •)                    ⋯ ϕ = e ⋯ ϕ •
([ c ]⇒ t)               ⋯ ϕ = [ c ⋯ ϕ ]⇒ t ⋯ ϕ
true                     ⋯ ϕ = true
false                    ⋯ ϕ = false
(e₁ ↓ e₂)                ⋯ ϕ = e₁ ⋯ ϕ ↓ e₂ ⋯ ϕ
Bool                     ⋯ ϕ = Bool
none                     ⋯ ϕ = none
(some e)                 ⋯ ϕ = some e ⋯ ϕ
case e [x→ e₁ ； e₂ ]    ⋯ ϕ = case e ⋯ ϕ [x→ e₁ ⋯ (ϕ ↑ _) ； e₂ ⋯ ϕ ]
(Maybe t)                ⋯ ϕ = Maybe t ⋯ ϕ

cong₃ : ∀ {l} {A B C D : Set l} (f : A → B → C → D) {x y u v p q} → 
        x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl

-- Can be derived in the full framework.
⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
⋯-id ⦃ K ⦄ (` x)             = `/`-is-` ⦃ K ⦄ x
⋯-id (λx e)                   = cong λx_ (trans (cong (e ⋯_) (~-ext id↑~id)) (⋯-id e))
⋯-id (Λα e)                   = cong Λα_ (trans (cong (e ⋯_) (~-ext id↑~id)) (⋯-id e))
⋯-id (∀α t)                   = cong ∀α_ (trans (cong (t ⋯_) (~-ext id↑~id)) (⋯-id t))
⋯-id (ζ t)                    = cong ζ_ (⋯-id t)
⋯-id (e₁ · e₂)                = cong₂ _·_ (⋯-id e₁) (⋯-id e₂)
⋯-id (e ∙)                    = cong _∙ (⋯-id e)
⋯-id (t₁ ⇒ t₂)                = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id (letrec e₂ ； e₁)        = cong₂ letrec_；_ (trans (cong (e₂ ⋯_) (~-ext id↑~id)) (⋯-id e₂)) (trans (cong (e₁ ⋯_) (~-ext id↑~id)) (⋯-id e₁))
⋯-id ★                        = refl
⋯-id (trait[o∶ t ] e)         = cong₂ trait[o∶_]_ (⋯-id t) (⋯-id e)
⋯-id (impl[ o ∶ t ] e₁ ； e₂) = cong₃ impl[ o ∶_]_；_ (⋯-id t) (⋯-id e₁) (⋯-id e₂)
⋯-id (ref o)                  = refl
⋯-id (o ∶ e)                  = cong (o ∶_) (⋯-id e)
⋯-id (ƛ[ c ] e)               = cong₂ ƛ[_]_ (⋯-id c) (trans (cong (e ⋯_) (~-ext id↑~id)) (⋯-id e))
⋯-id (e •)                    = cong _• (⋯-id e)
⋯-id ([ c ]⇒ t)               = cong₂ [_]⇒_ (⋯-id c) (⋯-id t)
⋯-id true                     = refl
⋯-id false                    = refl
⋯-id (e₁ ↓ e₂)                = cong₂ _↓_ (⋯-id e₁) (⋯-id e₂)
⋯-id Bool                     = refl
⋯-id none                     = refl
⋯-id (some e)                 = cong some_ (⋯-id e)
⋯-id case e [x→ e₁ ； e₂ ]    = cong₃ case_[x→_；_] (⋯-id e) (trans (cong (e₁ ⋯_) (~-ext id↑~id)) (⋯-id e₁)) (⋯-id e₂)
⋯-id (Maybe t)                = cong Maybe_ (⋯-id t)

SystemO-Traversal : Traversal
SystemO-Traversal = record
  { _⋯_ = _⋯_ ; ⋯-id = ⋯-id ; ⋯-var = λ x ϕ → refl }

open Traversal SystemO-Traversal hiding (_⋯_; ⋯-id)

⋯-fusion :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
⋯-fusion (` x) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (λx e) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (Λα e) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (∀α e) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (ζ e) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (e · e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (e ∙) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (e ⇒ e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (letrec e ； e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion ★ ϕ₁ ϕ₂ = {!   !}
⋯-fusion (trait[o∶ e ] e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (impl[ x ∶ e ] e₁ ； e₂) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (ref x) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (x ∶ e) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (ƛ[ e ] e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion (e •) ϕ₁ ϕ₂ = {!   !}
⋯-fusion ([ e ]⇒ e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion true ϕ₁ ϕ₂ = {!   !}
⋯-fusion false ϕ₁ ϕ₂ = {!   !}
⋯-fusion (e ↓ e₁) ϕ₁ ϕ₂ = {!   !}
⋯-fusion Bool ϕ₁ ϕ₂ = {!   !}
⋯-fusion none ϕ₁ ϕ₂ = {!   !}
⋯-fusion (some e) ϕ₁ ϕ₂ = {!   !}
⋯-fusion case e [x→ e₁ ； e₂ ] ϕ₁ ϕ₂ = {!   !}
⋯-fusion (Maybe e) ϕ₁ ϕ₂ = {!   !}

{-
-- Can be derived in the full framework.
SystemF-Traversal : Traversal
SystemF-Traversal = record
  { _⋯_ = _⋯_ ; ⋯-id = ⋯-id ; ⋯-var = λ x ϕ → refl }

open Traversal SystemF-Traversal hiding (_⋯_; ⋯-id)

-- Can be derived in the full framework.
⋯-fusion :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
  → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ·ₖ ϕ₂)
⋯-fusion (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
⋯-fusion (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion t₁ ϕ₁ ϕ₂)
                                          (⋯-fusion t₂ ϕ₁ ϕ₂)
⋯-fusion (λx t)         ϕ₁ ϕ₂ = cong λx_ (
  (t ⋯ (ϕ₁ ↑ 𝕖 n)) ⋯ (ϕ₂ ↑ 𝕖 n)   ≡⟨ ⋯-fusion t (ϕ₁ ↑ 𝕖 n) (ϕ₂ ↑ 𝕖 n) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕖 n) ·ₖ (ϕ₂ ↑ 𝕖 n))  ≡⟨ cong (t ⋯_) (sym (
                                   ~-ext (dist-↑-· 𝕖 n ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕖 n)        ∎)
⋯-fusion (Λ[α: l ] t)         ϕ₁ ϕ₂ = cong Λ[α: l ]_ (
  (t ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)
    ≡⟨ ⋯-fusion t (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕥) ·ₖ (ϕ₂ ↑ 𝕥))
    ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕥)
    ∎)
⋯-fusion (∀[α∶ l ] t₂) ϕ₁ ϕ₂ =
  cong ∀[α∶ l ]_ (
    (t₂ ⋯ (ϕ₁ ↑ 𝕥)) ⋯ (ϕ₂ ↑ 𝕥)
      ≡⟨ ⋯-fusion t₂ (ϕ₁ ↑ 𝕥) (ϕ₂ ↑ 𝕥) ⟩
    t₂ ⋯ ((ϕ₁ ↑ 𝕥) ·ₖ (ϕ₂ ↑ 𝕥))
      ≡⟨ cong (t₂ ⋯_) (sym (~-ext (dist-↑-· 𝕥 ϕ₁ ϕ₂))) ⟩
    t₂ ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕥)
      ∎)
⋯-fusion (t₁ ∙ t₂)      ϕ₁ ϕ₂ =
  cong₂ _∙_ (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)
⋯-fusion (t₁ ⇒ t₂)      ϕ₁ ϕ₂ =
  cong₂ _⇒_ (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)
⋯-fusion ★[ l ]              ϕ₁ ϕ₂ = refl

-- Can be derived in the full framework.
SystemF-CTraversal : ComposeTraversal
SystemF-CTraversal = record { ⋯-fusion = ⋯-fusion }

open ComposeTraversal SystemF-CTraversal hiding (⋯-fusion)

-- Type System -----------------------------------------------------------------

SystemF-Types : Types
SystemF-Types = record
  { ↑ᵗ = λ { 𝕖 n → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 ; 𝕖 n → _ , 𝕜 ; 𝕔 → _ , 𝕜  } }

open Types SystemF-Types

private variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢`  :  ∀ {x : S ∋ s} {T : S ∶⊢ s} →
         Γ ∋ x ∶ T →
         Γ ⊢ ` x ∶ T
  ⊢λ  :  ∀ {e : (𝕖 n ∷ S) ⊢ 𝕖 n} →
         (t₁ ∷ₜ Γ) ⊢ e ∶ (wk _ t₂) →
         Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ  :  (★[ l ] ∷ₜ Γ) ⊢ wk e ∶ t₂ →
         Γ ⊢ Λ[α: l ] e ∶ ∀[α∶ l ] t₂
  ⊢·  :  Γ ⊢ t₁ ∶ ★[ l ] →
         Γ ⊢ e₁ ∶ t₁ ⇒ t₂ →
         Γ ⊢ e₂ ∶ t₁ →
         Γ ⊢ e₁ · e₂ ∶ t₂
  ⊢∙  :  {Γ : Ctx S} →
         (★[ l ] ∷ₜ Γ) ⊢ t₁ ∶ ★[ l′ ] →
         Γ ⊢ t₂ ∶ ★[ l ] →
         Γ ⊢ e₁ ∶ ∀[α∶ l ] t₁ →
         Γ ⊢ e₁ ∙ t₂ ∶ t₁ ⋯ ⦅ t₂ ⦆
  ⊢⇒  :  Γ ⊢ t₁ ∶ ★[ l₁ ] → 
         Γ ⊢ t₂ ∶ ★[ l₂ ] →
         Γ ⊢ t₁ ⇒ t₂ ∶ ★[ l₁ ⊔ l₂ ]
  ⊢∀  :  (★[ l ] ∷ₜ Γ) ⊢ t ∶ ★[ l′ ] →
         Γ ⊢ ∀[α∶ l ] t ∶ ★[ Level.suc l ⊔ l′ ]

SystemF-Typing : Typing
SystemF-Typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing SystemF-Typing hiding (_⊢_∶_; ⊢`) 

_⊢⋯_ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ W : WkKit K ⦄ ⦃ TK : TypingKit K ⦄
    ⦃ C₁ : ComposeKit K Kᵣ K ⦄ ⦃ C₂ : ComposeKit K K K ⦄
    ⦃ C₃ : ComposeKit K Kₛ Kₛ ⦄
    {S₁ S₂ st} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort st}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ ϕ ∶ t ⋯ ϕ
⊢` ⊢x ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ {t₂ = t₂} ⊢e  ⊢⋯ ⊢ϕ =
  ⊢λ (subst  (_ ⊢ _ ∶_) (sym (⋯-↑-wk t₂ _ _))
             (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))
⊢Λ ⊢e ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢t₁ ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢· (⊢t₁ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢ϕ =
  subst  (_ ⊢ _ ∶_) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
         (⊢∙ (⊢t₁ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (⊢e₁ ⊢⋯ ⊢ϕ))
⊢⇒ ⊢τ₁ ⊢τ₂ ⊢⋯ ⊢ϕ = ⊢⇒ (⊢τ₁ ⊢⋯ ⊢ϕ) (⊢τ₂ ⊢⋯ ⊢ϕ)
⊢∀ ⊢τ ⊢⋯ ⊢ϕ = ⊢∀ (⊢τ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))

SystemF-TTraversal : TypingTraversal
SystemF-TTraversal = record { _⊢⋯_ = _⊢⋯_ }

open TypingTraversal SystemF-TTraversal hiding (_⊢⋯_)

-- Semantics -------------------------------------------------------------------

data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-λ   :  ∀ {e₂ : S ⊢ 𝕖 n} → (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
  β-Λ   :  ∀ {t₂ : S ⊢ 𝕥} → (Λ[α: l ] e₁) ∙ t₂ ↪ e₁ ⋯ ⦅ t₂ ⦆
  ξ-λ   :  e ↪ e' → λx e ↪ λx e'
  ξ-Λ   :  e ↪ e' → Λ[α: l ] e ↪ Λ[α: l ] e'
  ξ-·₁  :  e₁ ↪ e₁' → e₁ · e₂ ↪ e₁' · e₂
  ξ-·₂  :  e₂ ↪ e₂' → e₁ · e₂ ↪ e₁ · e₂'
  ξ-∙₁  :  e₁ ↪ e₁' → e₁ ∙ t₂ ↪ e₁' ∙ t₂

  
-- Subject Reduction -----------------------------------------------------------

subject-reduction : Γ ⊢ e ∶ t → e ↪ e' → Γ ⊢ e' ∶ t
subject-reduction (⊢· {t₂ = t₂} ⊢t₁ (⊢λ ⊢e₁) ⊢e₂) β-λ =
  subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆-⋯ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁)) β-Λ = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ
subject-reduction (⊢λ ⊢e) (ξ-λ e↪e') =
  ⊢λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢Λ ⊢e) (ξ-Λ e↪e') =
  ⊢Λ (subject-reduction ⊢e e↪e')
subject-reduction (⊢· ⊢t₁ ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') =
  ⊢· ⊢t₁ (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
subject-reduction (⊢· ⊢t₁ ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') =
  ⊢· ⊢t₁ ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁) (ξ-∙₁ e₁↪e₁') =
  ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')

-- Denotational Semantics ------------------------------------------------------

-- Envₜ : Ctx S → Setω
-- Envₜ {S = S} Γ = ∀ (l : Level) → (x : S ∋ 𝕥) → 
--   Γ ∋ x ∶ ★[ l ] →
--   Set l
-- 
-- variable η η′ η₁ η₂ η₃ : Envₜ Γ
-- 
-- extₜ : Envₜ Γ → Set l → Envₜ (_∷ₜ_ {s = 𝕥} ★[ l ] Γ)
-- extₜ Γ ⟦t⟧ _ _∋_.zero refl = ⟦t⟧
-- extₜ Γ ⟦t⟧ l (_∋_.suc x) ⊢x = Γ l x {!  !}
-- 
-- extₜ-t : Envₜ Γ → Envₜ (_∷ₜ_ {s = 𝕖 n} t Γ)
-- extₜ-t Γ _ (_∋_.suc x) ⊢x = Γ _ x {!   !}
-- 
-- ⟦_⟧ₜ : Γ ⊢ t ∶ ★[ l ] → Envₜ Γ → Set l
-- ⟦ ⊢` {x = x} ⊢x ⟧ₜ η = η _ x ⊢x
-- ⟦ ⊢⇒ ⊢t₁ ⊢t₂ ⟧ₜ η = ⟦ ⊢t₁ ⟧ₜ η → ⟦ ⊢t₂ ⟧ₜ η
-- ⟦ ⊢∀ {l = l} ⊢t ⟧ₜ η = (⟦t⟧ : Set l) → ⟦ ⊢t ⟧ₜ (extₜ η ⟦t⟧)
-- 
-- Envₑ : (Γ : Ctx S) → Envₜ Γ → Setω
-- Envₑ {S = S} Γ η = ∀ (l : Level) (x : S ∋ 𝕖 n) (t : S ⊢ 𝕥) (⊢t : Γ ⊢ t ∶ ★[ l ]) → 
--   Γ ∋ x ∶ t → 
--   ⟦ ⊢t ⟧ₜ η 
-- 
-- extₑ : ∀ {⊢t : Γ ⊢ t ∶ ★[ l ]} {η : Envₜ Γ} → 
--   Envₑ Γ η → 
--   ⟦ ⊢t ⟧ₜ η →
--   Envₑ (_∷ₜ_ {s = 𝕖 n} t Γ) (extₜ-t η)
-- extₑ Γ ⟦e⟧ = {!   !}
-- 
-- extₑ-t : ∀ {η : Envₜ Γ} → 
--   Envₑ Γ η → 
--   (⟦t⟧ : Set l) → 
--   Envₑ (_∷ₜ_ {s = 𝕥} ★[ l ] Γ) (extₜ η ⟦t⟧)
-- extₑ-t Γ ⟦t⟧ = {!   !}
-- 
-- ⟦_⟧ₑ : ∀ {η : Envₜ Γ} → 
--   (⊢e : Γ ⊢ e ∶ t) → 
--   (⊢t : Γ ⊢ t ∶ ★[ l ]) → 
--   Envₑ Γ η → 
--   ⟦ ⊢t ⟧ₜ η
-- ⟦ ⊢` {x = x} ⊢x ⟧ₑ ⊢t γ = γ _ x _ ⊢t ⊢x
-- ⟦ ⊢λ ⊢e ⟧ₑ (⊢⇒ ⊢t₁ ⊢t₂) γ = λ ⟦e⟧ → {! ⟦ ⊢e ⟧ₑ ? (extₑ {⊢t = ⊢t₁} γ ⟦e⟧) !}
-- ⟦ ⊢Λ ⊢e ⟧ₑ (⊢∀ ⊢t) γ = λ ⟦t⟧ → ⟦ ⊢e ⟧ₑ ⊢t (extₑ-t γ ⟦t⟧)
-- ⟦ ⊢· ⊢t₁ ⊢e₁ ⊢e₂ ⟧ₑ ⊢t γ = (⟦ ⊢e₁ ⟧ₑ (⊢⇒ ⊢t₁ ⊢t) γ) (⟦ ⊢e₂ ⟧ₑ ⊢t₁ γ)
-- ⟦_⟧ₑ {η = η} (⊢∙ ⊢t₁ ⊢t₂ ⊢e) ⊢t γ = {! (⟦ ⊢e ⟧ₑ (⊢∀ ⊢t₁) γ) (⟦ ⊢t₂ ⟧ₜ η) !} 
-}   