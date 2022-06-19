open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary

import Automaton

module EmptySet (Symbol : Set) (eq : Decidable {A = Symbol} _≡_) where

  open Automaton Symbol
  open NFA

  data EmptySet-State : Set where
    state-reject : EmptySet-State

  emptySet : NFA
  emptySet =
      record
        { State = EmptySet-State
        ; start = state-reject
        ; next = λ b state-reject → [ state-reject ]
        ; accept = λ state-reject → false
        }