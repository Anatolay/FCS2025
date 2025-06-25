import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture

namespace Learn
open Nat
open List


def notAnyHead
  (notAny : ¬(Any P (head :: tail)))
  : ¬(P head)
  := sorry

def notAnyTail
  (notAny : ¬(Any P (head :: tail)))
  : ¬(Any P tail)
  := sorry

def notAnyImpliesForAllNot
  (notAny : ¬(Any P xs))
  : All (λ x => ¬(P x)) xs
  := sorry


inductive Merge : List A → List A → List A → Type where
  | mergeNil : Merge nil nil nil
  | mergeLeft : Merge xs ys zs → Merge (x :: xs) ys (x :: zs)
  | mergeRight : Merge xs ys zs → Merge xs (y :: ys) (y :: zs)


def canSplit
  (zs : List A)
  : ∃ xs, ∃ ys, Merge xs ys zs
  := sorry


inductive Vector : Type → Nat → Type where
  | vectorNil : Vector A 0
  | vectorCons : A → Vector A n → Vector A (succ n)

def Vector.singleton
  (x : A)
  : Vector A 1
  := .vectorCons x .vectorNil

def Vector.head
  (vec : Vector A (succ n))
  : A
  := match vec with
    | .vectorCons x _ => x

def Vector.toList
  (vec : Vector A n)
  : List A
  := sorry

def Vector.fromList
  (xs : List A)
  : Vector A (sorry)
  := sorry
