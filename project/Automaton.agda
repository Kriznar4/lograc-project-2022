{-# OPTIONS --allow-unsolved-metas #-}

open import Data.List hiding (lookup)
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]')
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional hiding (map)
open import Data.List.Relation.Unary.Any hiding (map; lookup)
open import Data.Empty
open import Data.Unit
open import Data.Bool

module Automaton (Symbol : Set) where

  Word = List Symbol

  record NFA : Set₁ where
    field
      State : Set                         -- the type of states
      start : State                       -- starting state
      step : Symbol → State → State       -- transition function
      silent : State → List State         -- silent steps
      accept : State → Bool               -- is it an accepting state?

    data Accept : State → Word → Set where
      accept-[] : ∀ {s : State} → T (accept s) → Accept s []
      accept-silent : ∀ {s₁ s₂ : State} {w : Word} → s₂ ∈ silent s₁ → Accept s₂ w → Accept s₁ w
      accept-∷ : ∀ {s : State} {a : Symbol} {w : Word} → Accept (step a s) w → Accept s (a ∷ w)

    -- accept-⊆ : ∀ {ss₁ ss₂ : List State} → ss₁ ⊆ ss₂ → {w : Word} → Accept ss₁ w → Accept ss₂ w
    -- accept-⊆ = {!!}
    -- accept-⊆ ss₁⊆ss₂ (accept-[] s∈ss₁ t) = accept-[] (lookup ss₁⊆ss₂ s∈ss₁) t
    -- accept-⊆ {ss₁} {ss₂} ss₁⊆ss₂ (accept-∷ {a = a} p) = accept-∷ (accept-⊆ q p)
    --   where q : nexts a ss₁ ⊆ nexts a ss₂
    --         q = {!!}
