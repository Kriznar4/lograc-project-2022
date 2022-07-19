open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import Automaton

module Repeat (Symbol : Set) where

  open Automaton Symbol
  open NFA

  data Initial-State : Set where
    state-accept : Initial-State

  repeat : NFA → NFA
  repeat A =
    record
      { State = Initial-State ⊎ State A
      ; start = inj₁ state-accept
      ; next = λ { a (inj₁ s) → map inj₂ (next A a (start A))
                 ; a (inj₂ s) → concat (map maybe-initial (next A a s))
                 }
      ; accept = λ { (inj₁ _) → true ; (inj₂ _) → false }
      }
    where
      maybe-initial : State A → List (Initial-State ⊎ State A)
      maybe-initial s with accept A s
      ... | false = [ inj₂ s ]
      ... | true =  inj₂ s ∷ inj₁ state-accept ∷ []
