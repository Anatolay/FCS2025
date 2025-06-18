import FCS.Week1.Lecture
import FCS.Week2.Lecture

namespace Learn
open Nat

-------------------------------------------------
-------------------- RECAP ----------------------
-------------------------------------------------


def aImpliesAorB
  : A → A ∨ B
  := sorry

def bImpliesAorB
  : B → A ∨ B
  := sorry

def andSymm
  (and : A ∧ B)
  : B ∧ A
  := sorry

def andToAnd
  (and : A ∧ B)
  : A ∧ (B ∧ A)
  := sorry

def orSymm
  (or : A ∨ B)
  : B ∨ A
  := sorry

def orToOr
  (or : A ∨ B)
  : A ∨ (B ∨ A)
  := sorry

def andImpliesOr
  (and : A ∧ B)
  : A ∨ B
  := sorry

def XOR A B := A ∧ ¬B ∨ ¬A ∧ B

def xorImpliesNotAnd
  (xor : XOR A B)
  : ¬(A ∧ B)
  := sorry


-------------------------------------------------
---------------- QUANTIFIERS --------------------
-------------------------------------------------

/-
We could define the quantifier as follows:

inductive ForAll (p : α → Type) where
  | forall (f : (x : α) → p x)

However, it only wraps Lean's built-in function, so we will use it instead.
-/
def ForAll (p : α → Type) := (x : α) → p x

-- notation (priority := high) " ∀ " x " , " body => ForAll (λ x => body)
notation (priority := high) " ∀ " x " , " body => (x : _) → body
notation (priority := high) " ∀ " x " : " t " , " body => (x : t) → body


inductive Exists (p : α → Type) where
  | exists (x : α) (f : p x)

notation (priority := high) " ∃ " x " , " body => Exists (λ x => body)
notation (priority := high) " ∃ " x " : " t " , " body => Exists (λ x : t => body)


def ExcludedMiddle := ∀ Q, ¬¬Q → Q

def deMorgan4
  (em : ExcludedMiddle)
  (p : ¬(A ∧ B))
  : ¬A ∨ ¬B
  := em _ (λ x => let y := deMorgan2 x; p (And.mk (em _ y.first) (em _ y.second)))



-------------------------------------------------
------------------ EQUALITY ---------------------
-------------------------------------------------


-- For any `x`, we have a proof that `x = x`.
-- We use `≡` instead of `=` since the latter is reserved in Lean.
-- use \== for `≡` and \=== for `≣`
inductive Eq : {α : Type} → α → α → Type where
  | refl {α : Type} : (a : α) → Eq a a
infix:10 " ≡ " => Eq

-- A shorthand for cases when Lean can figure `x` on its own
def rfl
  : x ≡ x
  := .refl x


-- Properties of equality:
-- reflexivity,
def reflEq
  : x ≡ x
  := rfl
-- symmetry,
def Eq.symm
  (eq : x ≡ y)
  : y ≡ x
  :=  match eq with
  | .refl _ => rfl
-- transitivity
def Eq.trans
  (eq1 : x ≡ y)
  (eq2 : y ≡ z)
  : x ≡ z
  :=  match eq1, eq2 with
  | .refl _, .refl _ => rfl


def zeroEqZero : zero ≡ zero := rfl

def zeroNotOne
  : ¬(zero ≡ succ zero)
  := λ eq => by contradiction

def neqEqNeq
  (neq : ¬(x ≡ y))
  (eq : x ≡ z)
  : ¬(y ≡ z)
  := λ yz => neq (Eq.trans eq (Eq.symm yz))

def eqEqNeqNeq
  (ab : a ≡ b)
  (xy : x ≡ y)
  (neq : ¬(a ≡ x))
  : ¬(b ≡ y)
  := λ by' => neq (Eq.trans (Eq.trans ab by') (Eq.symm xy))

-- A simple function that just returns its argument
def id
  (x : α)
  := x

-- Lean is quite smart and will perform some computations for us,
-- e.g. substitute function call `id x` with the body of `id`:
def idEq
  : id x ≡ x
  := rfl


-- However, there is a limit to Lean's capabilities
def succEq
  (eq : n ≡ m)
  : succ n ≡ succ m
  -- := rfl -- fails
  := match eq with
  | .refl _ => rfl

def succEqReverse
  (eq : succ n ≡ succ m)
  : succ n ≡ succ m
  := match eq with
  | .refl _ => rfl


-- Two important properties of equality:
-- Substitution
def Eq.subst
  (P : α → Type)
  (eq : a ≡ b)
  (p : P a)
  : P b
  := match eq with
  | .refl _ => p
-- and congruence
def Eq.cong
  (P : α → β)
  (eq : a ≡ b)
  : P a ≡ P b
  := match eq with
  | .refl _ => rfl

def succEqSubst
  (eq : n ≡ m)
  : succ n ≡ succ m
  := Eq.subst
    (λ x => succ n ≡ succ x)
    eq
    rfl

def succEqCong
  (eq : n ≡ m)
  : succ n ≡ succ m
  := Eq.cong succ eq

def substExample
  {f : Nat → Nat}
  {x : Nat}
  (fx : f x ≡ 5)
  (xy : x ≡ y)
  : f y ≡ 5
  := Eq.subst (λ v => f v ≡ 5) xy fx

def congExample
  {f g : Nat → Nat}
  {x : Nat}
  (gx : g x ≡ 5)
  : f (g x) ≡ f 5
  := Eq.cong f gx

def congExample2
  {f : Nat → Nat → Nat}
  {g : Nat → Nat}
  {x y : Nat}
  (gx : g x ≡ 5)
  : f (g x) y ≡ f 5 y
  := Eq.cong (λ v => f v y) gx



-- Some magic to support chains of equalities in Lean.
-- You may simply ignore this
def stepSimple
  (x : α)
  {y : α}
  {r : α → α → Type}
  (xRy : r x y)
  : r x y
  := xRy
infixr:20 " ≣ " => stepSimple
notation:20 x " ≣⟨ " xy " ⟩ " yz => stepSimple x (Eq.trans xy yz)
notation:20 x " qed " => x ≣ rfl


def twoPlusTwo
  : 2 +ℕ 2 ≡ 4
  := 2 +ℕ 2
    ≣ succ 1 +ℕ 2
    ≣ succ (1 +ℕ 2)
    ≣ succ (succ 0 +ℕ 2)
    ≣ succ (succ (0 +ℕ 2))
    ≣ succ (succ 2)
    ≣ succ 3
    ≣ 4
    qed

/-
open Int

def onePlusOneInt
  : pos 1 +ℤ pos 1 ≡ pos 2
  := pos 1 +ℤ pos 1
    ≣⟨ by simp [addInt]; exact rfl ⟩ pos (1 +ℕ 1)
    ≣ pos (succ (0 +ℕ 1))
    ≣ pos (succ 1)
    ≣ pos 2
    qed
-/

-- Whenever we use ≣, we just explicitly write things that Lean
-- can figure out on its own.
def twoPlusTwo2
  : 2 +ℕ 2 ≡ 4
  := rfl

def addZeroLeft
  : 0 +ℕ n ≡ n
  := rfl

-- However, if there is an equality which Lean does not understand,
-- we can give a hint with the ≣⟨ hint ⟩ syntax.
-- use \< and \> (or just \<>) to typeset triangular parenthesis.
def addZeroRight
  : n +ℕ 0 ≡ n
  -- := rfl -- fails
  := match n with
  | 0 => rfl
  | succ m =>
      succ m +ℕ 0
      ≣ succ (m +ℕ 0)
      ≣⟨ Eq.cong succ addZeroRight ⟩ succ m
      qed

def addSuccRight
  : n +ℕ succ m ≡ succ (n +ℕ m)
  := match n with
  | 0 => rfl
  | succ n' =>
      succ n' +ℕ succ m
      ≣ succ (n' +ℕ succ m)
      ≣⟨ Eq.cong succ addSuccRight ⟩ succ (succ (n' +ℕ m))
      ≣ succ (succ n' +ℕ m)
      qed

def addNatSymm
  : n +ℕ m ≡ m +ℕ n
  := match n with
  | 0 =>
      0 +ℕ m
      ≣ m
      ≣⟨ Eq.symm addZeroRight ⟩ m +ℕ 0
      qed
  | succ n' => match m with
    | 0 =>
        succ n' +ℕ 0
        ≣ succ (n' +ℕ 0)
        ≣⟨ Eq.cong succ addZeroRight ⟩ succ n'
        qed
    | succ m' =>
        succ n' +ℕ succ m'
        ≣ succ (n' +ℕ succ m')
        ≣⟨ Eq.cong succ addNatSymm ⟩ succ (succ m' +ℕ n')
        ≣⟨ Eq.symm addSuccRight ⟩ succ m' +ℕ succ n'
        qed
