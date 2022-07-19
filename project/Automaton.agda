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
      next : Symbol → State → List State  -- transition function
      accept : State → Bool               -- is it an accepting state?

    nexts : Symbol → List State → List State
    nexts a ss = concat (map (next a) ss)

    data Accept : List State → Word → Set where
      accept-[] : ∀ {ss : List State} {s : State} → s ∈ ss → T (accept s) → Accept ss []
      accept-∷ : ∀ {ss : List State} {a : Symbol} {w : Word} → Accept (nexts a ss) w → Accept ss (a ∷ w)

    accept-⊆ : ∀ {ss₁ ss₂ : List State} → ss₁ ⊆ ss₂ → {w : Word} → Accept ss₁ w → Accept ss₂ w
    accept-⊆ ss₁⊆ss₂ (accept-[] s∈ss₁ t) = accept-[] (lookup ss₁⊆ss₂ s∈ss₁) t
    accept-⊆ {ss₁} {ss₂} ss₁⊆ss₂ (accept-∷ {a = a} p) = accept-∷ (accept-⊆ q p)
      where q : nexts a ss₁ ⊆ nexts a ss₂
            q = {!!}

  open NFA

  -- This is used to construct the concatenation of two automata
  maybe-jump : (A : NFA) → (B : NFA) → State A → List (State A ⊎ State B)
  maybe-jump A B s with accept A s
  ... | false = [ inj₁ s ]
  ... | true =  inj₁ s ∷ inj₂ (start B) ∷ []
