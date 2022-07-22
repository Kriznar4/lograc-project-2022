open import Data.List
open import Data.Bool
open import Relation.Binary

import Automaton

module EmptySymbol (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data Empty-State : Set where
    state-accept : Empty-State
    state-reject : Empty-State

  emptySymbol : NFA
  emptySymbol =
      record
        { State = Empty-State
        ; start = state-accept
        ; step = λ { _ state-accept → state-reject
                   ; _ state-reject → state-reject
                   }
        ; silent = λ _ → []
        ; accept = λ { state-accept → true
                     ; state-reject → false}
        }
