import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture


namespace Learn
open Nat
open List


inductive Typ where
  | ATyp
  | Arr (T₁ T₂ : Typ)
open Typ

infixr:20 " ⇒ " => Arr

def Context := List Typ

inductive Lookup : Context → Typ → Type where
  | here : Lookup (T :: tail) T
  | there
    : Lookup tail A
    → Lookup (B :: tail) A
open Lookup

notation Γ " ∋ " T => Lookup Γ T

inductive Term : Context → Typ → Type where
  | var : (Γ ∋ A) → Term Γ A
  | lam : Term (A :: Γ) B → Term Γ (Arr A B)
  | app : Term Γ (Arr A B) → Term Γ A → Term Γ B
open Term

-- λx:A.λy:A.x       OR         λA.λA.1
def example1
  : Term nil (ATyp ⇒ ATyp ⇒ ATyp)
  := lam (lam (var (there here)))
