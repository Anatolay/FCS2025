import FCS.Week1.Lecture

namespace Learn

open Nat

def multNat
  (n m : Nat)
  : Nat
  := sorry

infix:30 " *ℕ " => multNat
-- #eval succ (succ zero) *ℕ succ (succ zero)

-- nᵐ
def expNat
  (n m : Nat)
  : Nat
  := sorry

-- #eval expNat (succ (succ zero)) (succ (succ (succ zero)))

inductive LessOrEqNat : Nat → Nat → Type where

inductive LessThanNat : Nat → Nat → Type where

notation:10 l:10 " <ℕ " r:11 => (LessThanNat l r)
notation:10 l:10 " <=ℕ " r:11 => (LessOrEqNat l r)


inductive Int where
open Int

inductive IntEq : Int → Int → Type where
open IntEq

infix:25 " =ℤ " => IntEq

def incrementInt
  (n : Int)
  : Int
  := sorry

def decrementInt
  (n : Int)
  : Int
  := sorry

def isZeroInt
  (n : Int)
  : Bool
  := sorry

def intEqTransitive
  (nm : n =ℤ m)
  (mk : m =ℤ k)
  : n =ℤ k
  := sorry

def inject
  (n : Nat)
  : Int
  := sorry

def addInt
  (n m : Int)
  : Int
  := sorry

infix:30 " +ℤ " => addInt

def multInt
  (n m : Int)
  : Int
  := sorry

infix:30 " *ℤ " => multInt

inductive Rational where

inductive RationalEq : Rational → Rational → Type where
