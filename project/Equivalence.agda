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

module Equivalence (Symbol : Set) (eq : Decidable {A = Symbol} _≡_) where

  open RegExp Symbol
  open Automaton Symbol
  open Compile Symbol eq
  open NFA
  open 1-Symbol Symbol eq
  open EmptySymbol

  regexp-nfa : ∀ {r : RegExpr} {w : List Symbol} → Match r w → Accept (compile r) [ start (compile r) ] w
  regexp-nfa match-ε = accept-[] (here refl) tt

  regexp-nfa (match-^ {a}) with eq a a | inspect (eq a) a
  ... | yes p | [ ξ ]' = accept-∷ (subst (λ b → Accept (1-symbol a) ((if does b then state-accept ∷ [] else state-reject ∷ []) ++ []) []) (sym ξ)
                          (accept-[] (here refl) tt))
  ... | no q | _ =  ⊥-elim (q refl)

  regexp-nfa (match-⊕-l p) = {!   !}
  regexp-nfa (match-⊕-r p) = {!!}

  regexp-nfa (match-∙ p q) = {!  !}

  regexp-nfa match-*-[] = accept-[] (here refl) tt
  regexp-nfa (match-*-++ p q) = {!   !}

  nfa-regexp : ∀ (r : RegExpr) (w : List Symbol) → NFA.Accept (compile r) [ start (compile r) ] w → Match r w
  nfa-regexp r w p = {!!}


  sequence-step₂ : ∀ (r₁ r₂ : RegExpr) (w₂ : List Symbol) (ss₂ : List (State (compile r₂))) →
                Accept (compile r₂) ss₂ w₂ →
                Accept (compile (r₁ ∙ r₂)) (map inj₂ ss₂) w₂
  sequence-step₂ r₁ r₂ [] ss₂ (accept-[] {s = s} s∈ss₂ t) = accept-[] {s = inj₂ s} (∈-map⁺ inj₂ s∈ss₂) t
  sequence-step₂ r₁ r₂ (a ∷ w₂) ss₂ (accept-∷ q) =
    accept-∷ (subst (λ ss → Accept (compile (r₁ ∙ r₂)) ss w₂) (e ss₂) (sequence-step₂ r₁ r₂ w₂ (nexts (compile r₂) a ss₂) q) )
    where
      e : ∀ (ss : List (State (compile r₂))) → map inj₂ (nexts (compile r₂) a ss) ≡ nexts (compile (r₁ ∙ r₂)) a (map inj₂ ss)
      e [] = refl
      e (s ∷ ss) = {!!}

  sequence-step₁ : ∀ {r₁ r₂ : RegExpr} (w₁ w₂ : List Symbol) (ss₁ : List (State (compile r₁))) →
                Accept (compile r₁) ss₁ w₁ →
                Accept (compile r₂) [ start (compile r₂) ] w₂ →
                Accept (compile (r₁ ∙ r₂)) (concat (map (maybe-jump (compile r₁) (compile r₂)) ss₁)) (w₁ ++ w₂)
  sequence-step₁ {r₁} {r₂} [] w₂ ss₁ (accept-[] s∈ss₁ t) q = subst (Accept (compile (r₁ ∙ r₂)) _) e {!!}
    where e : [] ++ w₂ ≡ w₂
          e = {!!}
  sequence-step₁ (a ∷ w₁) w₂ ss₁ (accept-∷ p) q = accept-∷ (sequence-step₁ w₁ w₂ {!!} {!p!} {!!})


  sequence-lemma : ∀ {r₁ r₂ : RegExpr} {w₁ w₂ : List Symbol} →
                Accept (compile r₁) [ start (compile r₁) ] w₁ →
                Accept (compile r₂) [ start (compile r₂) ] w₂ →
                -----------------------------------------------
                Accept (compile (r₁ ∙ r₂)) [ start (compile (r₁ ∙ r₂)) ] (w₁ ++ w₂)
  sequence-lemma {r₁} {r₂} {[]} {w₂} = {!!}
  sequence-lemma {r₁} {r₂} {a ∷ w₁} {w₂} (accept-∷ p) q = accept-∷ {!sequence-lemmua!}

  -- sequence-lemma {r₁} {r₂} {w₁} {w₂} with (compile r₁)
  -- ... | record { State = State₁ ; start = start₁ ; next = next₁ ; accept = accept₁ } with (compile r₂)
  -- ... | record { State = State₂ ; start = start₂ ; next = next₂ ; accept = accept₂ } = {!   !}
