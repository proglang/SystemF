module StratifiedSystemF where

open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (ℕ; zero; suc) renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_; map)
open import Data.Fin using (Fin; zero; suc; _≟_; toℕ; lower₁)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open ≡-Reasoning

open import Kits

-- Fixities --------------------------------------------------------------------

infix   3  _⊢_  _,_↪_,_  _⊢_∶_ _Matches_ _Matches′_
infixr  5  λx_  Λα_  ∀α_ letx_；_ trait[o∶_]_ impl[_∶_]_；_ ƛ[_∶_]_ [_∶_]⇒_
infixr  6  _⇒_ _↓_  
infixl  6  _·_  
infix   6 _∙ _•
infix   7  `_ Maybe_ some_ ref_ 

-- Sorts -----------------------------------------------------------------------

data Sort : SortTy → Set where
  𝕖     : ℕ → Sort Var
  𝕥     : ℕ → Sort Var
  -- 𝕔     : ℕ → Sort Var
  𝕜     : Sort NoVar

-- Syntax ----------------------------------------------------------------------

private variable
  st st₁ st₂ st₃ st' st₁' st₂' : SortTy
  s s₁ s₂ s₃ s' s₁' s₂' s₃'    : Sort st
  S S₁ S₂ S₃ S' S₁' S₂' S₃'    : List (Sort Var)
  x y z x₁ x₂ α β γ            : S ∋ s
  n n₁ n₂ n'                   : ℕ
  o o₁ o₂                      : Fin n

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
  Λα_             : (𝕥 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n 
  ∀α_             : (𝕥 n ∷ S) ⊢ 𝕥 n → S ⊢ 𝕥 n 
  _·_             : S ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n
  _∙              : S ⊢ 𝕖 n → S ⊢ 𝕖 n 
  _⇒_             : S ⊢ 𝕥 n → S ⊢ 𝕥 n → S ⊢ 𝕥 n
  letx_；_        : S ⊢ 𝕖 n → (𝕖 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n -- need MUTUAL recursive block
  ★               : S ⊢ 𝕜
  -- Overloading
  trait[o∶_]_     : S ⊢ 𝕥 n → S ⊢ 𝕖 (suc n) → S ⊢ 𝕖 n -- rust would allow S ⊢ t ts (suc n), 
                                                      -- so maybe we should too?
  impl[_∶_]_；_   : Fin n → S ⊢ 𝕥 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n  -- need to couple impl with trait def
                                                                   -- for translation to mutual block
  ref_            : Fin n → S ⊢ 𝕖 n  
  -- Constraints 
  ƛ[_∶_]_         : Fin n → S ⊢ 𝕥 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n  
  _•              : S ⊢ 𝕖 n → S ⊢ 𝕖 n 
  [_∶_]⇒_         : Fin n → S ⊢ 𝕥 n → S ⊢ 𝕥 n → S ⊢ 𝕥 n
  -- Exemplary expressions & types
  true            : S ⊢ 𝕖 n 
  false           : S ⊢ 𝕖 n
  _↓_             : S ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n -- {nor} is a complete operator set for propositional logic 
  Bool            : S ⊢ 𝕥 n
  none            : S ⊢ 𝕖 n
  some_           : S ⊢ 𝕖 n → S ⊢ 𝕖 n
  case_[x→_；_]   : S ⊢ 𝕖 n → (𝕖 n ∷ S) ⊢ 𝕖 n → S ⊢ 𝕖 n → S ⊢ 𝕖 n
  Maybe_          : S ⊢ 𝕥 n → S ⊢ 𝕥 n

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
_ = letx λx λx (` zero ↓ ` zero) ↓ (` (suc zero) ↓ ` (suc zero)) ； 
    letx Λα λx λx λx 
          case `  (suc zero) [x→ case ` (suc zero) [x→ ` (suc (suc (suc (suc zero)))) · ` zero · ` (suc zero) ； false ] ； 
                             case ` zero [x→ false ； true ] ] ； 
    ` zero ∙ · ` (suc zero) · some true · some true

private variable
  e e₁ e₂ e₃ e' e₁' e₂'  : S ⊢ 𝕖 n
  t t₁ t₂ t₃ t' t₁' t₂'  : S ⊢ 𝕥 n
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
(` x)                    ⋯ σ = `/id (x & σ)
(λx e)                   ⋯ σ = λx e ⋯ (σ ↑ _)
(Λα e)                   ⋯ σ = Λα e ⋯ (σ ↑ _)
(∀α t)                   ⋯ σ = ∀α t ⋯ (σ ↑ _)
(e₁ · e₂)                ⋯ σ = e₁ ⋯ σ · e₂ ⋯ σ
(e ∙)                    ⋯ σ = e ⋯ σ ∙
(t₁ ⇒ t₂)                ⋯ σ = t₁ ⋯ σ ⇒ t₂ ⋯ σ
(letx e₂ ； e₁)          ⋯ σ = letx e₂ ⋯ σ ； e₁ ⋯ (σ ↑ _)
★                        ⋯ σ = ★
(trait[o∶ t ] e)         ⋯ σ = trait[o∶ t ⋯ σ ] e ⋯ σ
(impl[ o ∶ t ] e₁ ； e₂) ⋯ σ = impl[ o ∶ t ⋯ σ ] e₁ ⋯ σ ； e₂ ⋯ σ
(ref o)                  ⋯ σ = ref o
(ƛ[ o ∶ t ] e)           ⋯ σ = ƛ[ o ∶ t ⋯ σ ] e ⋯ σ
(e •)                    ⋯ σ = e ⋯ σ •
([ o ∶ t' ]⇒ t)           ⋯ σ = [ o ∶ t' ⋯ σ ]⇒ t ⋯ σ
true                     ⋯ σ = true
false                    ⋯ σ = false
(e₁ ↓ e₂)                ⋯ σ = e₁ ⋯ σ ↓ e₂ ⋯ σ
Bool                     ⋯ σ = Bool
none                     ⋯ σ = none
(some e)                 ⋯ σ = some e ⋯ σ
case e [x→ e₁ ； e₂ ]    ⋯ σ = case e ⋯ σ [x→ e₁ ⋯ (σ ↑ _) ； e₂ ⋯ σ ]
(Maybe t)                ⋯ σ = Maybe t ⋯ σ

cong₃ : ∀ {l} {A B C D : Set l} (f : A → B → C → D) {x y u v p q} → 
        x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl

-- Can be derived in the full framework.
⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
⋯-id ⦃ K ⦄ (` x)             = `/`-is-` ⦃ K ⦄ x
⋯-id (λx e)                   = cong λx_ (trans (cong (e ⋯_) (~-ext id↑~id)) (⋯-id e))
⋯-id (Λα e)                   = cong Λα_ (trans (cong (e ⋯_) (~-ext id↑~id)) (⋯-id e))
⋯-id (∀α t)                   = cong ∀α_ (trans (cong (t ⋯_) (~-ext id↑~id)) (⋯-id t))
⋯-id (e₁ · e₂)                = cong₂ _·_ (⋯-id e₁) (⋯-id e₂)
⋯-id (e ∙)                    = cong _∙ (⋯-id e)
⋯-id (t₁ ⇒ t₂)                = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id (letx e₂ ； e₁)          = cong₂ letx_；_(⋯-id e₂)
                                  (trans (cong (e₁ ⋯_) (~-ext id↑~id)) (⋯-id e₁))
⋯-id ★                        = refl
⋯-id (trait[o∶ t ] e)         = cong₂ trait[o∶_]_ (⋯-id t) (⋯-id e)
⋯-id (impl[ o ∶ t ] e₁ ； e₂) = cong₃ impl[ o ∶_]_；_ (⋯-id t) (⋯-id e₁) (⋯-id e₂)
⋯-id (ref o)                  = refl
⋯-id (ƛ[ o ∶ t ] e)           = cong₂ ƛ[ o ∶_]_ (⋯-id t) (⋯-id e)
                                  -- (trans (cong (e ⋯_) (~-ext id↑~id)) (⋯-id e))
⋯-id (e •)                    = cong _• (⋯-id e)
⋯-id ([ o ∶ t' ]⇒ t)          = cong₂ [ o ∶_]⇒_ (⋯-id t') (⋯-id t)
⋯-id true                     = refl
⋯-id false                    = refl
⋯-id (e₁ ↓ e₂)                = cong₂ _↓_ (⋯-id e₁) (⋯-id e₂)
⋯-id Bool                     = refl
⋯-id none                     = refl
⋯-id (some e)                 = cong some_ (⋯-id e)
⋯-id case e [x→ e₁ ； e₂ ]    = cong₃ case_[x→_；_] 
                                  (⋯-id e) 
                                  (trans (cong (e₁ ⋯_) (~-ext id↑~id)) (⋯-id e₁)) 
                                  (⋯-id e₂)
⋯-id (Maybe t)                = cong Maybe_ (⋯-id t)

SystemO-Traversal : Traversal
SystemO-Traversal = record
  { _⋯_ = _⋯_ ; ⋯-id = ⋯-id ; ⋯-var = λ x σ → refl }

open Traversal SystemO-Traversal hiding (_⋯_; ⋯-id)

-- Can be derived in the full framework.
⋯-fusion :
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
    (t : S₁ ⊢ s) (σ₁ : S₁ –[ K₁ ]→ S₂) (σ₂ : S₂ –[ K₂ ]→ S₃)
  → (t ⋯ σ₁) ⋯ σ₂ ≡ t ⋯ (σ₁ ·ₖ σ₂)
⋯-fusion (` x) σ₁ σ₂ = sym (&/⋯-⋯ (σ₁ _ x) σ₂)
⋯-fusion (λx e) σ₁ σ₂                   = cong λx_ (trans 
                                            (⋯-fusion e (σ₁ ↑ _) (σ₂ ↑ _)) 
                                            (cong (e ⋯_) (sym (~-ext (dist-↑-· _ σ₁ σ₂)))))
⋯-fusion (Λα e) σ₁ σ₂                   = cong Λα_ (trans 
                                            (⋯-fusion e (σ₁ ↑ _) (σ₂ ↑ _)) 
                                            (cong (e ⋯_) (sym (~-ext (dist-↑-· _ σ₁ σ₂)))))
⋯-fusion (∀α t) σ₁ σ₂                   = cong ∀α_ (trans 
                                            (⋯-fusion t (σ₁ ↑ _) (σ₂ ↑ _)) 
                                            (cong (t ⋯_) (sym (~-ext (dist-↑-· _ σ₁ σ₂)))))
-- ⋯-fusion (ζ t) σ₁ σ₂                    = cong ζ_ (⋯-fusion t σ₁ σ₂)
⋯-fusion (e₁ · e₂) σ₁ σ₂                = cong₂ _·_ (⋯-fusion e₁ σ₁ σ₂) (⋯-fusion e₂ σ₁ σ₂)
⋯-fusion (e ∙) σ₁ σ₂                    = cong _∙ (⋯-fusion e σ₁ σ₂)
⋯-fusion (t₁ ⇒ t₂) σ₁ σ₂                = cong₂ _⇒_ (⋯-fusion t₁ σ₁ σ₂) (⋯-fusion t₂ σ₁ σ₂)
⋯-fusion (letx e₂ ； e₁) σ₁ σ₂          = cong₂ letx_；_ (⋯-fusion e₂ σ₁ σ₂) (trans 
                                            (⋯-fusion e₁ (σ₁ ↑ _) (σ₂ ↑ _)) 
                                            (cong (e₁ ⋯_) (sym (~-ext (dist-↑-· _ σ₁ σ₂)))))
⋯-fusion ★ σ₁ σ₂                        = refl
⋯-fusion (trait[o∶ t ] e) σ₁ σ₂         = cong₂ trait[o∶_]_ (⋯-fusion t σ₁ σ₂) (⋯-fusion e σ₁ σ₂)
⋯-fusion (impl[ o ∶ t ] e₁ ； e₂) σ₁ σ₂ = cong₃ (impl[ o ∶_]_；_) (⋯-fusion t σ₁ σ₂) 
                                            (⋯-fusion e₁ σ₁ σ₂) (⋯-fusion e₂ σ₁ σ₂)
⋯-fusion (ref o) σ₁ σ₂                  = refl
⋯-fusion (ƛ[ o ∶ t ] e) σ₁ σ₂           = cong₂ ƛ[ o ∶_]_ (⋯-fusion t σ₁ σ₂) (⋯-fusion e σ₁ σ₂)
⋯-fusion (e •) σ₁ σ₂                    = cong _• (⋯-fusion e σ₁ σ₂)
⋯-fusion ([ o ∶ t' ]⇒ t) σ₁ σ₂          = cong₂ [ o ∶_]⇒_ (⋯-fusion t' σ₁ σ₂) (⋯-fusion t σ₁ σ₂)
⋯-fusion true σ₁ σ₂                     = refl
⋯-fusion false σ₁ σ₂                    = refl
⋯-fusion (e₁ ↓ e₂) σ₁ σ₂                = cong₂ _↓_ (⋯-fusion e₁ σ₁ σ₂) (⋯-fusion e₂ σ₁ σ₂)
⋯-fusion Bool σ₁ σ₂                     = refl
⋯-fusion none σ₁ σ₂                     = refl
⋯-fusion (some e) σ₁ σ₂                 = cong some_ (⋯-fusion e σ₁ σ₂)
⋯-fusion case e [x→ e₁ ； e₂ ] σ₁ σ₂    = cong₃ case_[x→_；_] (⋯-fusion e σ₁ σ₂) (trans 
                                            (⋯-fusion e₁ (σ₁ ↑ _) (σ₂ ↑ _)) 
                                            (cong (e₁ ⋯_) (sym (~-ext (dist-↑-· _ σ₁ σ₂))))) 
                                          (⋯-fusion e₂ σ₁ σ₂)
⋯-fusion (Maybe t) σ₁ σ₂                = cong Maybe_ (⋯-fusion t σ₁ σ₂)


SystemF-CTraversal : ComposeTraversal
SystemF-CTraversal = record { ⋯-fusion = ⋯-fusion }

open ComposeTraversal SystemF-CTraversal hiding (⋯-fusion)

-- Type System -----------------------------------------------------------------

SystemF-Types : Types
SystemF-Types = record
  { ↑ᵗ = λ { (𝕖 n) → _ , 𝕥 n
           ; (𝕥 n) → _ , 𝕜
          
           ; 𝕜 → _ , 𝕜 } }

open Types SystemF-Types

private variable
  Γ Γ₁ Γ₂ Γ' Γ₁' Γ₂' : Ctx S
  T T₁ T₂ T' T₁' T₂' : S ∶⊢ s

{-
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
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] σ ∶ Γ₁ →
  Γ₂ ⊢ e ⋯ σ ∶ t ⋯ σ
⊢` ⊢x ⊢⋯ ⊢σ = ⊢`/id (⊢σ _ _ ⊢x)
⊢λ {t₂ = t₂} ⊢e  ⊢⋯ ⊢σ =
  ⊢λ (subst  (_ ⊢ _ ∶_) (sym (⋯-↑-wk t₂ _ _))
             (⊢e ⊢⋯ (⊢σ ∋↑/⊢↑ _)))
⊢Λ ⊢e ⊢⋯ ⊢σ = ⊢Λ (⊢e ⊢⋯ (⊢σ ∋↑/⊢↑ _))
⊢· ⊢t₁ ⊢e₁ ⊢e₂ ⊢⋯ ⊢σ = ⊢· (⊢t₁ ⊢⋯ ⊢σ) (⊢e₁ ⊢⋯ ⊢σ) (⊢e₂ ⊢⋯ ⊢σ)
⊢∙ {t₁ = t₁} {t₂ = t₂} ⊢t₁ ⊢t₂ ⊢e₁ ⊢⋯ ⊢σ =
  subst  (_ ⊢ _ ∶_) (sym (dist-↑-⦅⦆-⋯ t₁ t₂ _))
         (⊢∙ (⊢t₁ ⊢⋯ (⊢σ ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢σ) (⊢e₁ ⊢⋯ ⊢σ))
⊢⇒ ⊢τ₁ ⊢τ₂ ⊢⋯ ⊢σ = ⊢⇒ (⊢τ₁ ⊢⋯ ⊢σ) (⊢τ₂ ⊢⋯ ⊢σ)
⊢∀ ⊢τ ⊢⋯ ⊢σ = ⊢∀ (⊢τ ⊢⋯ (⊢σ ∋↑/⊢↑ _))

SystemF-TTraversal : TypingTraversal
SystemF-TTraversal = record { _⊢⋯_ = _⊢⋯_ }

open TypingTraversal SystemF-TTraversal hiding (_⊢⋯_)
-}  


-- Semantics -------------------------------------------------------------------

data Val : S ⊢ 𝕖 n → Set where
  V-λ     : Val (λx e)
  V-ƛ     : Val (ƛ[ o ∶ t ] e)
  V-Λ     : Val (Λα e)
  V-true  : Val {S = S} {n = n} true 
  V-false : Val {S = S} {n = n} false 
  V-some  : Val e → Val (some e)
  V-none  : Val {S = S} {n = n} none

data WeakCanonical : S ⊢ 𝕖 n → S ⊢ 𝕥 n → Set where
  WC-∀ : WeakCanonical e t → WeakCanonical (Λα e) (∀α t)
  WC-ƛ : WeakCanonical e t → WeakCanonical (ƛ[ o ∶ t' ] e) ([ o ∶ t' ]⇒ t) 
  WC-λ : WeakCanonical e (t₁ ⇒ t₂)

⋯wc : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → (σ : S₁ –[ K ]→ S₂) → WeakCanonical e t → WeakCanonical (e ⋯ σ) (t ⋯ σ)
⋯wc σ (WC-∀ wc) = WC-∀ (⋯wc (σ ↑ _) wc) 
⋯wc σ (WC-ƛ wc) = WC-ƛ (⋯wc σ wc)
⋯wc σ WC-λ      = WC-λ

Impl : (List (Sort Var)) → ℕ → Set 
Impl S n = Σ[ t ∈ S ⊢ 𝕥 n ] Σ[ e ∈ S ⊢ 𝕖 n ] WeakCanonical e t -- × Val e (not neccessary i guess)

Store : List (Sort Var) → ℕ → Set
Store S n = Fin n → List (Impl S n)

ext : Store S n → Store S (suc n)
ext {n = n} Σ zero = []
ext {n = n} Σ (suc x) = {!   !}

impl : Store S n → Fin n → Impl S n → Store S n 
impl S x i n with x ≟ n 
... | yes refl = i ∷ S n
... | no _     = S n

_⇑_ : Store S n → (s : Sort Var) → Store (s ∷ S) n
(Σ ⇑ s) n = map (λ { (t , e , wc) → wk _ t , wk _ e , ⋯wc (λ _ → suc) wc }) (Σ n)

variable 
  Σ Σ₁ Σ₂ Σ₁' Σ₂' Σ' Σ'' : Store S n

data _Matches′_ : S ⊢ 𝕖 n → S ⊢ 𝕥 n → Set where
  λ-⇒        : λx e Matches′ t₁ ⇒ t₂
  some-Maybe : some e Matches′ Maybe t
  none-Maybe : none Matches′ Maybe t
  true-Bool  : true {S = S} {n = n} Matches′ Bool 
  false-Bool : false {S = S} {n = n} Matches′ Bool 

data _Matches_ : S ⊢ 𝕖 n → S ⊢ 𝕥 n → Set where
  ∀α-skip    : ∀{e : S ⊢ 𝕖 n} → wk _ e Matches t → e Matches ∀α t 
  []⇒-skip   : e Matches t → e Matches [ o ∶ t' ]⇒ t
  ⇒-skip     : e Matches′ t₁ → e Matches t₁ ⇒ t₂

_∋_,_ : Store S n → Fin n → S ⊢ 𝕖 n → Set
_∋_,_ Σ o e = ∃[ t ] ∃[ e' ] ∃[ wc ] (t , e' , wc) ∈ Σ o × e Matches t  

-- preserves syntax direction but might block some proofs later on 
-- might prefer non-deterministic typing rules? 
reduce : ∀{e : S ⊢ 𝕖 n} → Σ ∋ o , e → S ⊢ 𝕖 n
reduce {e = e} (t , e' , wc , _ , matches) = go wc e matches
  where go : ∀ {t : S ⊢ 𝕥 n} {e' : S ⊢ 𝕖 n} → WeakCanonical e' t → (e : S ⊢ 𝕖 n) → e Matches t → S ⊢ 𝕖 n
        go (WC-∀ wc) e (∀α-skip matches)                    = (Λα (go wc (wk _ e) matches)) ∙ 
        go (WC-ƛ {o = o} {t' = t'} wc) e ([]⇒-skip matches) = (ƛ[ o ∶ t' ] (go wc e matches)) •
        go {e' = e'} WC-λ e (⇒-skip matches′)               = e' · e -- matches' is already evidence that this app works

data _,_↪_,_ : Store S n → S ⊢ 𝕖 n → Store S n' → S ⊢ 𝕖 n' → Set where
  β-λ : ∀ {e₂ : S ⊢ 𝕖 n} →
    Val e₂ →
    Σ , (λx e₁) · e₂ ↪ Σ , e₁ ⋯ ⦅ e₂ ⦆ 
  β-Λ : ∀ {e : 𝕥 n ∷ S ⊢ 𝕖 n} → 
    (t : S ⊢ 𝕥 n) →
    Σ , (Λα e) ∙ ↪ Σ , e ⋯ ⦅ t ⦆ 
  β-ƛ : 
    Σ , (ƛ[ o ∶ t ] e) • ↪ Σ , e
  β-let : ∀ {e₂ : S ⊢ 𝕖 n} →
    Val e₂ →  
    Σ , letx e₂ ； e₁ ↪ Σ , (e₁ ⋯ ⦅ e₂ ⦆)
  β-case₁ : ∀ {e : S ⊢ 𝕖 n} →
    Val e →
    Σ , case some e [x→ e₁ ； e₂ ] ↪ Σ , e₁ ⋯ ⦅ e ⦆ 
  β-case₂ :
    Σ , case none [x→ e₁ ； e₂ ] ↪ Σ , e₂ 
  β-trait : 
    Σ , trait[o∶ t ] e ↪ ext Σ , e
  β-impl :
    Val e₁ →
    (wc : WeakCanonical e₁ t) → -- actually this ensures this is Val
    Σ , impl[ o ∶ t ] e₁ ； e₂ ↪ impl Σ o (t , e₁ , wc) , e₂ 
  
-- Subject Reduction -----------------------------------------------------------

-- subject-reduction : Γ ⊢ e ∶ t → e ↪ e' → Γ ⊢ e' ∶ t
-- subject-reduction (⊢· {t₂ = t₂} ⊢t₁ (⊢λ ⊢e₁) ⊢e₂) β-λ =
--   subst (_ ⊢ _ ∶_) (wk-cancels-⦅⦆-⋯ t₂ _) (⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ)
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ (⊢Λ ⊢e₁)) β-Λ = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢t₂ ⦆ₛ
-- subject-reduction (⊢λ ⊢e) (ξ-λ e↪e') =
--   ⊢λ (subject-reduction ⊢e e↪e')
-- subject-reduction (⊢Λ ⊢e) (ξ-Λ e↪e') =
--   ⊢Λ (subject-reduction ⊢e e↪e')
-- subject-reduction (⊢· ⊢t₁ ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e₁') =
--   ⊢· ⊢t₁ (subject-reduction ⊢e₁ e₁↪e₁') ⊢e₂
-- subject-reduction (⊢· ⊢t₁ ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e₂') =
--   ⊢· ⊢t₁ ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂')
-- subject-reduction (⊢∙ ⊢t₁ ⊢t₂ ⊢e₁) (ξ-∙₁ e₁↪e₁') =
--   ⊢∙ ⊢t₁ ⊢t₂ (subject-reduction ⊢e₁ e₁↪e₁')

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