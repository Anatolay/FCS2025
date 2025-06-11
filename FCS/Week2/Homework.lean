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

def XOR (A B: Type) := False

def xorImpliesOr
  (xor : XOR A B)
  : A ∨ B
  := sorry

def ExcludedMiddle := False

def negateExists
  (A : Type)
  (P : A → Type)
  (ne : ¬ (∃ x, P x))
  : ∀ x, ¬(P x)
  := sorry

/-
Not provable:
def notForAll
  (A : Type)
  (P : A → Type)
  (nfa : ¬ (∀ x : A, P x))
  : ∃ x : A, ¬ (P x)
  := sorry
-/

def threeByTwo
  : 2 *ℕ 3 ≡ 6
  := sorry

def addNatAssoc
  : (x +ℕ y) +ℕ z ≡ x +ℕ (y +ℕ z)
  := sorry


def exclMidImpliesOr
  (em : ExcludedMiddle)
  : P ∨ ¬P
  -- := em (P ∨ ¬P) (λ np => let npnnp := deMorgan2 np; npnnp.second npnnp.first)
  := sorry

def deMorgan4
  (em : ExcludedMiddle)
  (p : ¬(A ∧ B))
  : ¬A ∨ ¬B
  := sorry
