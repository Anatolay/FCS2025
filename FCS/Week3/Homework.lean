import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture

namespace Learn
open Nat

def notExists
  {A : Type}
  {P : A → Type}
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

def exclMidImpliesOr
  (em : ExcludedMiddle)
  : P ∨ ¬P
  := sorry


def addNatAssoc
  : (x +ℕ y) +ℕ z ≡ x +ℕ (y +ℕ z)
  := match x with
  | zero => sorry
  | succ n =>
      (succ n +ℕ y) +ℕ z
      ≣ succ ((n +ℕ y) +ℕ z)
      ≣⟨ sorry ⟩ succ (n +ℕ (y +ℕ z))
      ≣ succ n +ℕ (y +ℕ z)
      qed

def LE  n m := ∃ k : Nat, n +ℕ succ k ≡ m
def LEQ n m := ∃ k : Nat, n +ℕ k ≡ m

def twoLeqThree
  : LEQ 2 3
  := sorry

def twoLeThree
  : LE 2 3
  := sorry

def leqLeft
  (ex : ∃ k, k +ℕ n ≡ m)
  : LEQ n m
  := sorry

def LeImpliesLeq
  (le : LE n m)
  : LEQ n m
  := sorry

def leqTrans
  (nm : LEQ n m)
  (mk : LEQ m k)
  : LEQ n k
  := match nm with
    | .exists d1 p1 => match mk with
      | .exists d2 p2 =>
          .exists
          (d1 +ℕ d2)
          (
            n +ℕ (d1 +ℕ d2)
            ≣⟨ sorry ⟩ (n +ℕ d1) +ℕ d2
            ≣⟨ sorry ⟩ m +ℕ d2
            ≣⟨ sorry ⟩ k
            qed
          )

def leTrans
  (nm : LE n m)
  (mk : LE m k)
  : LE n k
  := sorry
