open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary
open import Data.Maybe hiding (map)

import Automaton

module Repeat (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data RepeatState (S : Set) : Set where
    repeat-start : RepeatState S
    repeat-reject : RepeatState S
    repeat-original : S → RepeatState S

  repeat : NFA → NFA
  repeat A =
    record
      { State = RepeatState (State A)
      ; start = repeat-start
      ; step = λ { _ repeat-start → repeat-reject
                 ; _ repeat-reject → repeat-reject
                 ; a (repeat-original s) → repeat-original (step A a s)
                 }
      ; silent = repeat-silent
      ; accept = λ { repeat-start → true
                   ; repeat-reject → false
                   ; (repeat-original _) → false }
      }
     where
       repeat-silent : RepeatState (State A) → List (RepeatState (State A))
       repeat-silent repeat-start = [ repeat-original (start A) ]
       repeat-silent repeat-reject = []
       repeat-silent (repeat-original s) with accept A s
       ... | false = map repeat-original (silent A s)
       ... | true =  repeat-start ∷ map repeat-original (silent A s)
