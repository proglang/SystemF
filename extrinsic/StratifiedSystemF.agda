module StratifiedSystemF where

-- open import Level using (Level) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)

open ≡-Reasoning

open import Kits

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _↪_  _⊢_∶_
infixr  5  λx_  Λα_  ∀α_ def_；_ trait[o∶_]_；_ impl_；_ some_ Maybe_ ƛ[_]_ [_]⇒_
infixr  6  _⇒_ _↓_ _∶α⇒_ 
infixl  6  _·_  _∙_ _•[_]_
infix   7  `_ ⇝_

-- Sorts -----------------------------------------------------------------------

data Sort : SortTy → Set where
  𝕖     : Sort Var
  𝕥     : Sort Var
  𝕠     : Sort Var
  𝕔     : Sort Var
  𝕚     : Sort NoVar
  𝕜     : Sort NoVar

-- Syntax ----------------------------------------------------------------------

private variable
  st                         : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'  : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'  : List (Sort Var)
  x y z x₁ x₂                : S ∋ s

data _⊢_ : List (Sort Var) → Sort st → Set where
  -- System F
  `_              : S ∋ s → S ⊢ s                
  λx_             : (𝕖 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖          
  Λα_             : (𝕥 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖 
  ∀α_             : (𝕥 ∷ S) ⊢ 𝕥 → S ⊢ 𝕥 
  _·_             : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖
  _∙_             : S ⊢ 𝕖 → S ⊢ 𝕥 → S ⊢ 𝕖 
  _⇒_             : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥
  def_；_         : S ⊢ 𝕖 → (𝕖 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖
  ★               : S ⊢ 𝕜
  -- Overloading
  trait[o∶_]_；_  : S ⊢ 𝕥 → (𝕠 ∷ S) ⊢ 𝕚 → (𝕠 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖
  impl_；_        : S ⊢ 𝕖 → S ⊢ 𝕚 → S ⊢ 𝕚
  ∅               : S ⊢ 𝕚
  _•[_]_          : S ⊢ 𝕠 → S ⊢ 𝕖 → S ⊢ 𝕖
  ⇝_              : S ⊢ 𝕚 → S ⊢ 𝕠 
  _,_             : S ⊢ 𝕥 → S ⊢ 𝕥 → S ⊢ 𝕥   
  -- Constraints 
  _∶α⇒_           : S ⊢ 𝕠 → S ⊢ 𝕥 → S ⊢ 𝕔
  ƛ[_]_           : S ⊢ 𝕔 → (𝕔 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖  
  [_]⇒_           : S ⊢ 𝕔 → S ⊢ 𝕥 → S ⊢ 𝕥
  -- Exemplary expressions & types
  true            : S ⊢ 𝕖 
  false           : S ⊢ 𝕖
  _↓_             : S ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖 -- {nor} is a complete operator set for propositional logic 
  𝔹               : S ⊢ 𝕥
  none            : S ⊢ 𝕖
  some_           : S ⊢ 𝕖 → S ⊢ 𝕖
  case_[x→_；_]   : S ⊢ 𝕖 → (𝕖 ∷ S) ⊢ 𝕖 → S ⊢ 𝕖 → S ⊢ 𝕖
  Maybe_          : S ⊢ 𝕥 → S ⊢ 𝕥

-- example program with overloading:
-- 
-- ```
-- trait eq : ∀α. α → α → Bool 
--
-- impl eq for Bool → Bool → Bool with
--      eq x y = x ↔ y
-- impl eq for ∀α. [eq : α → α → Bool] → Maybe α → Maybe α → Bool
--      eq (some x) (some y) = eq x y 
--      eq none     none     = true
--      eq _        _        = false
--
-- eq (some true) (some true)
-- ``` 
--
-- attempt #1:
-- 
-- _ : [] ⊢ 𝕖
-- _ = trait[o∶ ∀α ` zero ⇒ ` zero ⇒ 𝔹 ] 
--       impl ` zero ∶ -- ∶ 𝔹 ⇒ 𝔹 ⇒ 𝔹 (is given by implementation)
--         λx λx (` zero ↓ ` zero) ↓ (` (suc zero) ↓ ` (suc zero)) ； -- (x₁ ↓ x₁) ↓ (x₂ ↓ x₂) ≡ x₁ ↔ x₂
--       impl ` zero ∶ -- ∶ ∀α [ suc zero ∶ (` zero ⇒ ` zero ⇒ 𝔹) ]⇒ Maybe ` zero ⇒ (Maybe ` zero) ⇒ 𝔹 
--         Λα ƛ[ ` suc zero ∶α⇒ ` zero ⇒ 𝔹 ] λx λx 
--             case ` (suc zero) 
--               [x→ case ` (suc zero) [x→ ` suc (suc (suc (suc (suc (suc zero))))) •[ ∅ ] ` zero · ` suc zero ； false ] ； 
--               case ` zero [x→ false ； true ] ] ； 
--       (` zero •[ 𝔹 , ∅ ] (some true) · (some true))
-- 
-- attempt #2:
_ : [] ⊢ 𝕖 
_ = trait[o∶ ∀α ` zero ⇒ ` zero ⇒ 𝔹 ] 
      impl λx λx 
        (` zero ↓ ` zero) ↓ (` (suc zero) ↓ ` (suc zero)) ； 
      impl Λα ƛ[ ` suc zero ∶α⇒ ` zero ⇒ 𝔹 ] λx λx 
        case ` (suc zero) 
          [x→  case ` (suc zero) [x→ ` suc (suc (suc (suc (suc (suc zero))))) •[  ] ` (suc zero) · ` zero ； false ] ； 
          case ` zero [x→ false ； true ] ] ； ∅ ； 
    {!   !}


private variable
  e e₁ e₂ e₃ e' e₁' e₂'  : S ⊢ 𝕖
  t t₁ t₂ t₃ t' t₁' t₂'  : S ⊢ 𝕥
  c c₁ c₂ c₃ c' c₁' c₂'  : S ⊢ 𝕔
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
(` x)                  ⋯ ϕ = `/id (x & ϕ)
(λx e)                 ⋯ ϕ = λx e ⋯ (ϕ ↑ 𝕖)
(Λα e)                 ⋯ ϕ = Λα e ⋯ (ϕ ↑ 𝕥)
(∀α t)                 ⋯ ϕ = ∀α t ⋯ (ϕ ↑ 𝕥)
(e₁ · e₂)              ⋯ ϕ = e₁ ⋯ ϕ · e₂ ⋯ ϕ
(e ∙ t)                ⋯ ϕ = e ⋯ ϕ ∙ t ⋯ ϕ
(t₁ ⇒ t₂)              ⋯ ϕ = t₁ ⋯ ϕ ⇒ t₂ ⋯ ϕ
(def e₂ ； e₁)         ⋯ ϕ = def e₂ ⋯ ϕ ； e₁ ⋯ (ϕ ↑ 𝕖)
★                      ⋯ ϕ = ★
-- (trait[o∶ c ] t)       ⋯ ϕ = trait[o∶ c ⋯ ϕ ] t ⋯ (ϕ ↑ 𝕠)
-- (impl o ∶ e₁ ； e₂)    ⋯ ϕ = impl o ⋯ ϕ ∶ e₁ ⋯ ϕ ； e₂ ⋯ ϕ
-- (o •[ ts ] e)          ⋯ ϕ = o ⋯ ϕ  •[ ts ⋯ ϕ ] e ⋯ ϕ
-- ∅                      ⋯ ϕ = ∅
-- (t , ts)               ⋯ ϕ = t ⋯ ϕ , ts ⋯ ϕ
-- (o ∶α⇒ e)              ⋯ ϕ = o ⋯ ϕ ∶α⇒ e ⋯ ϕ
-- (ƛ[ c ] e)             ⋯ ϕ = ƛ[ c ⋯ ϕ ] e ⋯ (ϕ ↑ 𝕔)
-- ([ c ]⇒ t)             ⋯ ϕ = [ c ⋯ ϕ ]⇒ t ⋯ ϕ
e                      ⋯ ϕ = {!   !}
true                   ⋯ ϕ = true
false                  ⋯ ϕ = false
(e₁ ↓ e₂)              ⋯ ϕ = e₁ ⋯ ϕ ↓ e₂ ⋯ ϕ
𝔹                      ⋯ ϕ = 𝔹
none                   ⋯ ϕ = none
(some e)               ⋯ ϕ = some (e ⋯ ϕ)
case e [x→ e₁ ； e₂ ]  ⋯ ϕ = case (e ⋯ ϕ) [x→  e₁ ⋯ (ϕ ↑ 𝕖) ； e₂ ⋯ ϕ  ]
(Maybe e)              ⋯ ϕ = Maybe (e ⋯ ϕ)

{-
-- Can be derived in the full framework.
⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
⋯-id (λx t)          = cong λx_ (
  t ⋯ (id ↑ 𝕖)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
  t ⋯ id        ≡⟨ ⋯-id t ⟩
  t             ∎)
⋯-id (Λ[α: l ] t)    = cong Λ[α: l ]_ (
  t ⋯ (id ↑ 𝕥)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
  t ⋯ id        ≡⟨ ⋯-id t ⟩
  t             ∎)
⋯-id (∀[α∶ l ] t₂)  = cong ∀[α∶ l ]_ (
  t₂ ⋯ (id ↑ 𝕥)  ≡⟨ cong (t₂ ⋯_) (~-ext id↑~id) ⟩
  t₂ ⋯ id        ≡⟨ ⋯-id t₂ ⟩
  t₂             ∎)
⋯-id (t₁ ∙ t₂)       = cong₂ _∙_ (⋯-id t₁) (⋯-id t₂)
⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id ★[ l ]          = refl

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
  (t ⋯ (ϕ₁ ↑ 𝕖)) ⋯ (ϕ₂ ↑ 𝕖)   ≡⟨ ⋯-fusion t (ϕ₁ ↑ 𝕖) (ϕ₂ ↑ 𝕖) ⟩
  t ⋯ ((ϕ₁ ↑ 𝕖) ·ₖ (ϕ₂ ↑ 𝕖))  ≡⟨ cong (t ⋯_) (sym (
                                   ~-ext (dist-↑-· 𝕖 ϕ₁ ϕ₂))) ⟩
  t ⋯ ((ϕ₁ ·ₖ ϕ₂) ↑ 𝕖)        ∎)
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
  { ↑ᵗ = λ { 𝕖 → _ , 𝕥 ; 𝕥 → _ , 𝕜 ; 𝕜 → _ , 𝕜 ; 𝕠 → _ , 𝕜 ; 𝕔 → _ , 𝕜  } }

open Types SystemF-Types

private variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢`  :  ∀ {x : S ∋ s} {T : S ∶⊢ s} →
         Γ ∋ x ∶ T →
         Γ ⊢ ` x ∶ T
  ⊢λ  :  ∀ {e : (𝕖 ∷ S) ⊢ 𝕖} →
         (t₁ ∷ₜ Γ) ⊢ e ∶ (wk _ t₂) →
         Γ ⊢ λx e ∶ t₁ ⇒ t₂
  ⊢Λ  :  (★[ l ] ∷ₜ Γ) ⊢ e ∶ t₂ →
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
  β-λ   :  ∀ {e₂ : S ⊢ 𝕖} → (λx e₁) · e₂ ↪ e₁ ⋯ ⦅ e₂ ⦆
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
-- extₜ-t : Envₜ Γ → Envₜ (_∷ₜ_ {s = 𝕖} t Γ)
-- extₜ-t Γ _ (_∋_.suc x) ⊢x = Γ _ x {!   !}
-- 
-- ⟦_⟧ₜ : Γ ⊢ t ∶ ★[ l ] → Envₜ Γ → Set l
-- ⟦ ⊢` {x = x} ⊢x ⟧ₜ η = η _ x ⊢x
-- ⟦ ⊢⇒ ⊢t₁ ⊢t₂ ⟧ₜ η = ⟦ ⊢t₁ ⟧ₜ η → ⟦ ⊢t₂ ⟧ₜ η
-- ⟦ ⊢∀ {l = l} ⊢t ⟧ₜ η = (⟦t⟧ : Set l) → ⟦ ⊢t ⟧ₜ (extₜ η ⟦t⟧)
-- 
-- Envₑ : (Γ : Ctx S) → Envₜ Γ → Setω
-- Envₑ {S = S} Γ η = ∀ (l : Level) (x : S ∋ 𝕖) (t : S ⊢ 𝕥) (⊢t : Γ ⊢ t ∶ ★[ l ]) → 
--   Γ ∋ x ∶ t → 
--   ⟦ ⊢t ⟧ₜ η 
-- 
-- extₑ : ∀ {⊢t : Γ ⊢ t ∶ ★[ l ]} {η : Envₜ Γ} → 
--   Envₑ Γ η → 
--   ⟦ ⊢t ⟧ₜ η →
--   Envₑ (_∷ₜ_ {s = 𝕖} t Γ) (extₜ-t η)
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