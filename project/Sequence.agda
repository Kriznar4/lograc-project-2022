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
      ; next = λ { a (inj₁ s) → concat (map (maybe-jump A B) (next A a s))
                 ; a (inj₂ s) → map inj₂ (next B a s)
                 }
      ; accept = λ { (inj₁ _) → false ; (inj₂ s) → accept B s }
      }
