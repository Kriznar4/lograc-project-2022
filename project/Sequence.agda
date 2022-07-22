open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import Automaton

module Sequence (Symbol : Set) where

  open Automaton Symbol
  open NFA

  sequence : NFA → NFA → NFA
  sequence A B =
    record
      { State = State A ⊎ State B
      ; start =  inj₁ (start A)
      ; step = λ { a (inj₁ s) → inj₁ (step A a s)
                 ; a (inj₂ s) → inj₂ (step B a s)
                 }
      ; silent = sequence-silent
      ; accept = λ { (inj₁ _) → false ; (inj₂ s) → accept B s }
      }
      where
        sequence-silent : State A ⊎ State B → List (State A ⊎ State B)
        sequence-silent (inj₁ s) with accept A s
        ... | false = map inj₁ (silent A s)
        ... | true = inj₂ (start B) ∷ map inj₁ (silent A s)
        sequence-silent (inj₂ s) = map inj₂ (silent B s)
