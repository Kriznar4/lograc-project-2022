open import Data.List
open import Data.Bool
open import Relation.Binary

import Automaton

module EmptySet (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data EmptySet-State : Set where
    state-reject : EmptySet-State

  emptySet : NFA
  emptySet =
      record
        { State = EmptySet-State
        ; start = state-reject
        ; next = λ _ state-reject → [ state-reject ]
        ; accept = λ state-reject → false
        }
