import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture
import FCS.Week5.Lecture

namespace Learn
open Nat
open List
open Term

def neqByMem
  (mem : x ∈ xs)
  (notMem : ¬(y ∈ xs))
  : ¬(x ≡ y)
  := sorry

-- (λx. (λy.y) x) (λz.z) ⇝* λz.z
def reduction1
  : (\ "x" => (\ "y" => var "y") @ var "x") @ (\ "z" => var "z") ⇝* \ "z" => var "z"
  := sorry

-- (λx. (λy.y) x) (λz.z) ⇝* λz.z
def reduction2
  : (\ "x" => (\ "y" => var "y") @ var "x") @ (\ "z" => var "z") ⇝* \ "z" => var "z"
  := sorry

/-
zz = pair c0 c0
ss = λp. pair (inc (fst p)) (fst p)
pred = λn. snd (n ss zz)

# n - m
minus = λn.λm.??

# n == m
numEq = λn.λm.??
-/

def callByValueSub
  (red : t ⇒ u)
  : t ⇝ u
  := sorry
