import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture
import FCS.Week6.Lecture

namespace Learn
open Nat
open List
open Term


-- Keep as sorry
def substitutionKeepsType
  (tTyp : (⟨x, A⟩ :: Γ) ⊢ t ⋮ B)
  (vTyp : Γ ⊢ v ⋮ A)
  : Γ ⊢ [x ↦ v]t ⋮ B
  := sorry


def preservation
  (wellTyped : nil ⊢ t ⋮ T)
  (reduce : t ⇝ u)
  : nil ⊢ u ⋮ T
  := match reduce with
    | _ => sorry
