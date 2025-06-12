import FCS.Week1.Lecture
import FCS.Week1.Homework

namespace Learn

open Nat

-------------------------------------------------
--------- LOGICAL CONNECTIVES -------------------
-------------------------------------------------

-- To prove "A and B", we need two proofs:
-- a proof of A and a proof of B.
structure And (α β : Type) where
  first : α
  second : β
infix:30 (priority := high) " ∧ " => And


def consumeAnd
  (and : A ∧ B)
  (f : A → B → C)
  : C
  := sorry

-- To prove "A or B", we need one of two proofs:
-- either a proof of A or a proof of B.
inductive Or (α β : Type) where
  | left (a : α)
  | right (b : β)
infix:20 (priority := high) " ∨ " => Or


def consumeOr
  (or : A ∨ B)
  (f : A → C)
  (g : B → C)
  : C
  := sorry

-- "A implies B" means that we can construct a proof of B when we have a proof of A.
-- A function from A to B does exactly that
def Imply (α β : Type) := α → β

-- If A, then (if B then A)
def tautology
  : Imply A (Imply B A)
  := λ x => λ _ => x


def Iff (α β : Type) := (α → β) ∧ (β → α)
infix:5 (priority := high) " <=> " => Iff

-- False is a special incorrect statement.
-- It has no values hence it can never be proven.
inductive False

-- If we have a value of type False, which should be impossible,
-- then we have arrived at a contradiction.
def absurd
  (f : False)
  : α
  := by contradiction

-- Suppose that we have a function from A to False.
-- Suppose that we have a value of type A.
-- Then we apply the function to the value and get a value of type False,
-- which is impossible. Contradiction.
-- It means that if we actually have the function, then
-- there does not exist a value of type A.
def Not (α : Type) := α → False
prefix:40 (priority := high) "¬ " => Not


def atMostOne
  : ¬(A ∧ ¬A)
  -- := λ ana => ana.second ana.first
  := λ ana => match ana with
    | { first, second } => second first

-- if A, then not not A
def tautology2
  : Imply A (¬¬A)
  := sorry

-- We cannot proof the Law of excluded middle:
-- (¬¬P) → P ─ not provable!
-- However, we can prove the for negative P (if P = ¬Q for some Q).
-- In other words, we can prove (¬¬¬P) → (¬P)
def excludedMiddleInNeg
  (P : Type)
  (nnnp : ¬¬¬P)
  : ¬P
  := λ p => nnnp (λ np => np p)

-- If not A and not B, the not (A or B)
def deMorgan1
  (p : ¬A ∧ ¬B)
  : ¬(A ∨ B)
  := λ aob => match aob with
    | .left a => p.first a
    | .right b => p.second b

def deMorgan2
  (nab : ¬(A ∨ B))
  : ¬A ∧ ¬B
  := sorry

def deMorgan
  : Iff (¬A ∧ ¬B) (¬(A ∨ B))
  := And.mk deMorgan1 deMorgan2
