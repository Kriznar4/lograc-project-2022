open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import Automaton

module Parallel (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data ParallelState (S : Set) (T : Set) : Set where
    silent-start : ParallelState S T
    silent-reject : ParallelState S T
    silent-left : S → ParallelState S T
    silent-right : T → ParallelState S T

  parallel : NFA → NFA → NFA
  parallel A B =
    record
      { State = ParallelState (State A) (State B)
      ; start =  silent-start
      ; step = λ { a silent-start → silent-reject
                 ; a silent-reject → silent-reject
                 ; a (silent-left s) → silent-left (step A a s)
                 ; a (silent-right s) → silent-right (step B a s)
                 }
      ; silent = λ { silent-start → silent-left (start A) ∷ silent-right (start B) ∷ []
                   ; silent-reject → []
                   ; (silent-left s) → map silent-left (silent A s)
                   ; (silent-right s) → map silent-right (silent B s)
                   }
      ; accept = λ { silent-start → false
                   ; silent-reject → false
                   ; (silent-left s) → accept A s
                   ; (silent-right s) → accept B s}
      }
