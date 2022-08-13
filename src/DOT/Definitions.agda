module DOT.Definitions (TypeLabel : Set) (TermLabel : Set) where

open import Data.Nat
open import Data.List as L using (List; []; _∷_)

data Avar : Set where
  Bound : ℕ → Avar
  --Free : Var → Avar

data Label : Set where
  LabelType : TypeLabel → Label
  LabelTerm : TermLabel → Label

mutual
  data Type : Set where
    ⊤ : Type
    ⊥ : Type
    ⦃⟨_⟩⦄ : Dec → Type
    _∧_ : Type → Type → Type
    _∙_ : Avar → TypeLabel → Type
    μ_ : Type → Type
    -- Note that we use ℿ instead of ∀ because ∀ is a keyword in Agda
    ℿ_∙_ : Type → Type

  data Dec : Set where
    _∶_∙∙_ : TypeLabel → Type → Type → Dec
    _∶_ : TermLabel → Type → Dec

mutual
  data Term : Set where
    ○_ : Avar → Term
    ●_ : Val → Term
    _∙_ : Avar → TermLabel →  Term
    _∘_ : Avar → Avar → Term
    --let_in_ : Term → Term → Term

  data Val : Set where
    ν_∙_ : Type → Defs → Val
    ƛ_∙_ : Type → Term → Val

  data Def : Set where
    ⦃⟨_==#_⟩⦄ : TypeLabel → Type → Def
    ⦃⟨_===_⟩⦄ : TermLabel → Term → Def

  Defs : Set
  Defs = List Def

labelOfDef : Def → Label
labelOfDef ⦃⟨ l ==# _ ⟩⦄ = LabelType l
labelOfDef ⦃⟨ m === _ ⟩⦄ = LabelTerm m
