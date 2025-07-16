import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture
import FCS.Week6.DeBruijn


namespace Learn
open Nat
open List

-- Decidability
inductive Decidable (A : Type) where
  | yes : A → Decidable A
  | no : ¬A → Decidable A

def eqNat
  (n m : Nat)
  : Bool
  := match n, m with
    | 0, 0 => true
    | succ _, 0 => false
    | 0, succ _ => false
    | succ m', succ n' => eqNat m' n'

def natEqDecidable
  (n m : Nat)
  : Decidable (n ≡ m)
  := match n, m with
    | 0, 0 => .yes rfl
    | succ _, 0 => .no (λ eq => by contradiction)
    | 0, succ _ => .no (λ eq => by contradiction)
    | succ n', succ m' => match natEqDecidable n' m' with
      | .yes eq => match eq with | .refl _ => .yes rfl
      | .no neq =>
          .no (λ eq => match eq with | .refl _ => neq rfl)

class ToDecidable (A : Type) where
  toDec : Decidable A

instance { n m : Nat } : ToDecidable (n ≡ m) where
  toDec := natEqDecidable n m

def ite
  (A : Type)
  [dec : ToDecidable A]
  (t e : C)
  : C
  := match dec.toDec with
    | .yes _ => t
    | .no _ => e

def dite
  {A : Type}
  (dec : Decidable A)
  (t : A → C)
  (e : ¬A → C)
  : C
  := match dec with
    | .yes a => t a
    | .no na => e na

notation:10 (priority := high) " if " c " then " t " else " e => ite c t e

def exa
  (n m : Nat)
  : Nat
  := if n ≡ m then 0 else 1
  -- := if natEqDecidable n m then 0 else 1

-- def compare
--   {A : Type}
--   [BEq A]
--   (x y : A)
--   : Bool
--   := x == y

-- def decAnd
  -- (decA : Decidable A)
  -- (decB : Decidable B)
  -- : Decidable (A ∧ B)
  -- := _


-------------
-- Rewrite Systems
-------

-- def diamond
--   (t : Term)
--   (red₁ : t ⇝ u)
--   (red₂ : t ⇝ s)
--   : ∃ w, u ⇝ w ∧ s ⇝ w

-- def confluence
--   (t : Term)
--   (red₁ : t ⇝* u)
--   (red₂ : t ⇝* s)
--   : ∃ w, u ⇝* w ∧ s ⇝* w

-- structure Rewrite where
--   A : Type
--   r : A → A → Type

-- def deBruijnRewrite
  -- : Rewrite
  -- := ⟨ DeBruijn, Reduce ⟩

def Rewrite A := A → A → Type

def deBruijnRewrite
  : Rewrite DeBruijn
  := Reduce

-- a ⇝ b  and  a ⇝ c   then   b ⇝ d  and  c ⇝ d   for some d
def Diamond (r : Rewrite A)
  := { a b c : A } → r a b → r a c → ∃ d, r b d ∧ r c d

-- inductive ReduceRTC : Term → Term → Type where
  -- | refl : ReduceRTC t t
  -- | trans : (t ⇝ u) → ReduceRTC u s → ReduceRTC t s
inductive RTC {A : Type} (r : Rewrite A) : A → A → Type where
  -- x ⇝* x
  | refl : RTC r x x
  --    x ⇝  y
  --    y ⇝* z
  -- => x ⇝* z
  | trans : r x y → RTC r y z → RTC r x z

-- a ⇝* b  and  a ⇝* c   then   b ⇝* d  and  c ⇝* d   for some d
def Confluence (r : Rewrite A)
  := { a b c : A } → RTC r a b → RTC r a c → ∃ d, RTC r b d ∧ RTC r c d

-- a ⇝* b  and  a ⇝ c   then   b ⇝* d  and  c ⇝* d   for some d
def SemiDiamond (r : Rewrite A)
  := { a b c : A } → RTC r a b → r a c → ∃ d, RTC r b d ∧ RTC r c d

def diamond_implies_semidiamond'
  {r : A → A → Type}
  (diamond : Diamond r)
  (a b c : A)
  (ab : RTC r a b)
  (ac : r a c)
  : ∃ d, RTC r b d ∧ RTC r c d
  := sorry

def Idempotent (f : A → A) := { x : A } → f (f x) ≡ f x

def diamond_implies_semidiamond
  (diamond : Diamond r)
  : SemiDiamond r
  := λ ab ac => diamond_implies_semidiamond' diamond _ _ _ ab ac

def diamond_implies_confluence'
  {r : A → A → Type}
  (diamond : Diamond r)
  (a b c : A)
  (ab : RTC r a b)
  (ac : RTC r a c)
  : ∃ d, RTC r b d ∧ RTC r c d
  := sorry

def diamond_implies_confluence
  (diamond : Diamond r)
  : Confluence r
  := λ ab ac => diamond_implies_confluence' diamond _ _ _ ab ac
