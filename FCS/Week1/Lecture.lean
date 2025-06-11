namespace Learn

-- inductive Nat where
  -- | zero
  -- | succ (n : Nat)

inductive Nat : Type where
  | zero : Nat
  | succ : (n : Nat) → Nat
open Nat

instance : OfNat Nat 0 where
  ofNat := zero

instance [OfNat Nat n] : OfNat Nat (n + 1) where
  ofNat := succ (inferInstance : OfNat Nat n).ofNat

def one := succ zero
def two := succ (succ zero)
def three := succ two

def incrementNat
  (n : Nat)
  : Nat
  := succ n

def decrementNat
  (n : Nat)
  : Nat
  := match n with
  | zero => zero
  | succ m => m

def isZeroNat
  (n : Nat)
  : Bool
  := match n with
  | zero => true
  | _ => false

def addNat
  (n m : Nat)
  : Nat
  := match n with
    | zero => m
    | succ k => succ (addNat k m)

infix:60 " +ℕ " => addNat
#eval addNat (succ zero) (succ zero) -- Learn.Nat.succ (Learn.Nat.succ (Learn.Nat.zero))


inductive NatEq : Nat → Nat → Type where
  | zeroEq : NatEq zero zero
  | succEq : NatEq n m → NatEq (succ n) (succ m)
open NatEq

infix:10 " =ℕ " => NatEq

def oneEqOne
  : succ zero =ℕ succ zero
  := succEq zeroEq

def oneEqZeroPlusOne
  : succ zero =ℕ incrementNat zero
  := succEq zeroEq

-- NOTE: Unpleasant visually, 'NatEq n n' vs 'n =ℕ n'
-- def natEqReflexive
  -- (n : Nat)
  -- : NatEq n n
  -- := sorry

def natEqReflexive
  (n : Nat)
  : n =ℕ n
  := match n with
    | zero => zeroEq -- P(0) ─ induction base
    | succ k =>      -- P(n) => P(n+1) ─ induction step
      let k_eqs_k := natEqReflexive k -- P(k) ─ induction hypothesis
      succEq k_eqs_k -- P(k+1) ─ step that follows from the hypothesis

-- NOTE: The following implementation fails due to non-termination
-- def natEqReflexive
--   (n : Nat)
--   : n =ℕ n
--   := natEqReflexive n

def natEqSymmetric
  (eq : n =ℕ m)
  : m =ℕ n
  := match eq with
    | zeroEq => zeroEq
    | succEq e =>
      let m'_eqs_n' := natEqSymmetric e
      succEq m'_eqs_n'

def natEqTransitive
  (n_eqs_m : n =ℕ m)
  (m_eqs_k : m =ℕ k)
  : (n =ℕ k)
  := match n_eqs_m with
    | zeroEq => match m_eqs_k with
      | zeroEq => zeroEq
    | succEq e1 => match m_eqs_k with
      | succEq e2 =>
        let n'_eqs_m' := natEqTransitive e1 e2
        succEq n'_eqs_m'
