open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import Automaton

module 1-Symbol (Symbol : Set) (eq : Decidable {A = Symbol} _≡_) where

  open Automaton Symbol
  open NFA

  data 1-State : Set where
    state-start : 1-State
    state-accept : 1-State
    state-reject : 1-State

  1-symbol : Symbol → NFA
  1-symbol a =
      record
        { State = 1-State
        ; start = state-start
        ; step = λ { b state-start →  if does (eq a b) then state-accept else state-reject
                   ; b state-accept → state-reject
                   ; b state-reject → state-reject
                   }
        ; silent = λ _ → []
        ; accept = λ { state-start → false
                     ; state-accept → true
                     ; state-reject → false}
        }
