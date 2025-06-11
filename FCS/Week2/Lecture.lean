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

-------------------------------------------------
----------------- QUANTIFIERS -------------------
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

/-
The following statements are implementation-dependent.
Since inequality was a part of the homework, this will be
commented out

def existsGreater
  : ∀ n, ∃ m, n <=ℕ m
  := λ n => .exists (succ n) (.leqSucc .leqSelf)

def zeroLeq
  : ∀ n, (0 <=ℕ n)
  := λ n => match n with
  | 0 => .leqSelf
  | succ m => .leqSucc (zeroLeq m)

-- For all k, if n <= m, then k + n <= k + m
def preserveIneq
  : ∀ k, n <ℕ m → k +ℕ n <ℕ k +ℕ m
  := λ k => λ less => match k with
    | 0 => less
    | succ r => .lessSucc (preserveIneq r less)

def succKeepsLeq
  (leq : n <=ℕ m)
  : succ n <=ℕ succ m
  := match leq with
    | .leqSelf => .leqSelf
    | .leqSucc leq' => .leqSucc (succKeepsLeq leq')

-- For all k, if n <= m, then k + n <= k + m
def preserveLeq
  : ∀ k, n <=ℕ m → k +ℕ n <=ℕ k +ℕ m
  := λ k => λ leq => match k with
    | 0 => leq
    | succ r => succKeepsLeq (preserveLeq r leq)
-/


-------------------------------------------------
------------------ EQUALITY ---------------------
-------------------------------------------------


-- For any `x`, we have a proof that `x = x`.
-- We use `≡` instead of `=` since the latter is reserved in Lean.
-- use \== for `≡` and \=== for `≣`
inductive Eq : α → α → Type where
  | refl : (a : α) → Eq a a
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
def symmEq
  (eq : x ≡ y)
  : y ≡ x
  :=  match eq with
  | .refl _ => rfl
-- transitivity
def tranEq
  (eq1 : x ≡ y)
  (eq2 : y ≡ z)
  : x ≡ z
  :=  match eq1, eq2 with
  | .refl _, .refl _ => rfl


def zeroEqZero : zero ≡ zero := rfl

def zeroNotOne
  : ¬(zero ≡ succ zero)
  := λ eq => by contradiction

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
notation:20 x " ≣⟨ " xy " ⟩ " yz => stepSimple x (tranEq xy yz)
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
      ≣⟨ symmEq addZeroRight ⟩ m +ℕ 0
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
        ≣⟨ symmEq addSuccRight ⟩ succ m' +ℕ succ n'
        qed
