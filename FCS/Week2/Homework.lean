import FCS.Week1.Lecture
import FCS.Week1.Homework
import FCS.Week2.Lecture

namespace Learn
open Nat

-- If not A or not B, the not (A and B)
def deMorgan3
  (p : ¬A ∨ ¬B)
  : ¬(A ∧ B)
  := sorry

/-
The following of De Morgan's Laws cannot be proven:
def deMorgan4
  (p : ¬(A ∧ B))
  : ¬A ∨ ¬B
  := sorry
-/

def disjunctiveSyllogism
  (or : P ∨ Q)
  (np : ¬P)
  : Q
  := sorry

def orToImplication
  (or : ¬X ∨ Y)
  : X → Y
  := sorry

def xorImpliesOr
  (xor : (A ∧ ¬B) ∨ (B ∧ ¬A))
  : A ∨ B
  := sorry

-- Curcly braces "{" and "}" make type `A`, `B`, and `X` implicit
-- Thus, when you call `andToOr`, instead of passing the types
-- as in `andToOr A B X someAnd`, you can simply write `andToOr someAnd`
def andToOr
  {A B X : Type}
  (axAndBx : (A → X) ∧ (B → X))
  : (A ∨ B) → X
  := sorry

def orToAnd
  {A B X : Type}
  (orToX : (A ∨ B) → X)
  : (A → X) ∧ (B → X)
  := sorry

def andIffOr
  {A B X : Type}
  : (A → X) ∧ (B → X) <=> (A ∨ B) → X
  := And.mk sorry sorry
