open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Bool
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]')
open import Relation.Binary
open import Relation.Nullary
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
import 1-Symbol

import RegExp
import Automaton
import Compile
import EmptySymbol
import Parallel

module Equivalence (Symbol : Set) (eq : Decidable {A = Symbol} _≡_) where

  open RegExp Symbol
  open Automaton Symbol
  open Compile Symbol eq
  open NFA
  open 1-Symbol Symbol eq
  open EmptySymbol

  module SequenceStep {r₁ r₂ : RegExpr} where

    sequence-step₂ : ∀ {w₂ : List Symbol} {s₂ : State (compile r₂)} →
                  Accept (compile r₂) s₂ w₂ →
                  Accept (compile (r₁ ∙ r₂)) (inj₂ s₂) w₂
    sequence-step₂ (accept-[] t) = accept-[] t
    sequence-step₂ (accept-silent p q) = accept-silent (∈-map⁺ inj₂ p) (sequence-step₂ q)
    sequence-step₂ (accept-∷ p) = accept-∷ (sequence-step₂ p)

    sequence-step₁ : ∀ {w₁ w₂ : List Symbol} {s₁ : State (compile r₁)} →
                  Accept (compile r₁) s₁ w₁ →
                  Accept (compile r₂) (start (compile r₂)) w₂ →
                  Accept (compile (r₁ ∙ r₂)) (inj₁ s₁) (w₁ ++ w₂)
    sequence-step₁ (accept-[] t) q = accept-silent {!  !} (sequence-step₂ q)
    sequence-step₁ (accept-silent e p) q = accept-silent {!  !} (sequence-step₁ p q)
    sequence-step₁ (accept-∷ p) q = accept-∷ (sequence-step₁ p q)

  module ParallelStep {r₁ r₂ : RegExpr} where
    parallel-stepₗ : ∀ {w : List Symbol} {s₁ : State (compile r₁)} →
                  Accept (compile r₁) s₁ w →
                  Accept (compile (r₁ ⊕ r₂)) (Parallel.silent-left s₁) w
    parallel-stepₗ (accept-[] t)  = accept-[] t
    parallel-stepₗ (accept-silent p q) = accept-silent (∈-map⁺ Parallel.silent-left p) (parallel-stepₗ q)
    parallel-stepₗ (accept-∷ p) = accept-∷ (parallel-stepₗ p)

    parallel-stepᵣ : ∀ {w : List Symbol} {s₂ : State (compile r₂)} →
                  Accept (compile r₂) s₂ w →
                  Accept (compile (r₁ ⊕ r₂)) (Parallel.silent-right s₂) w
    parallel-stepᵣ (accept-[] t)  = accept-[] t
    parallel-stepᵣ (accept-silent p q) = accept-silent (∈-map⁺ Parallel.silent-right p) (parallel-stepᵣ q)
    parallel-stepᵣ (accept-∷ p) = accept-∷ (parallel-stepᵣ p)
  
  open SequenceStep 
  open ParallelStep

  regexp-nfa : ∀ {r : RegExpr} {w : List Symbol} → Match r w → Accept (compile r) (start (compile r) ) w
  regexp-nfa match-ε = accept-[] tt
  regexp-nfa (match-^ {a}) with eq a a | inspect (eq a) a
  ... | yes p | [ ξ ]' = accept-∷ (subst (λ b → Accept (1-symbol a) (if does b then state-accept else state-reject) []) (sym ξ) (accept-[] tt))
  ... | no q | _ = ⊥-elim (q refl)
  regexp-nfa (match-⊕-l p) = {!   !}
  -- regexp-nfa (match-⊕-l p) = accept-silent {!  !} (parallel-stepₗ (regexp-nfa p))
  regexp-nfa (match-⊕-r p) = {!   !}
  regexp-nfa { r₁ ∙ r₂ } { w } (match-∙ p q)  = {!   !} 
  -- for some reason this gets blocked
  -- regexp-nfa (match-∙ p q) = sequence-step₁ (regexp-nfa p) (regexp-nfa q)
  -- how to get r₁, r₂, w₁ and w₂ in context? and also r₁ = r₁ etc.?
  -- { r₁ = r₁ } { r₂ = r₂ }

  regexp-nfa match-*-[] = accept-[] tt
  regexp-nfa (match-*-++ p q) = {!   !}



  nfa-regexp : ∀ (r : RegExpr) (w : List Symbol) → NFA.Accept (compile r) (start (compile r) ) w → Match r w
  nfa-regexp r w p = {!!}


  
      