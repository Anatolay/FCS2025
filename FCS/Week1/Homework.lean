import FCS.Week1.Lecture

namespace Learn

open Nat

def multNat
  (n m : Nat)
  : Nat
  := sorry

infix:70 " *ℕ " => multNat
-- #eval succ (succ zero) *ℕ succ (succ zero)

-- nᵐ
def expNat
  (n m : Nat)
  : Nat
  := sorry

-- #eval expNat (succ (succ zero)) (succ (succ (succ zero)))

inductive LessOrEqNat : Nat → Nat → Type where

inductive LessThanNat : Nat → Nat → Type where

infix:50 " <ℕ " => LessThanNat
infix:50 " <=ℕ " => LessOrEqNat


inductive Int where
open Int

deriving instance Repr for Nat, Int
-- #eval pos (succ zero)

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

def inject
  (n : Nat)
  : Int
  := sorry

def addInt
  (n m : Int)
  : Int
  := sorry

infix:60 " +ℤ " => addInt

def multInt
  (n m : Int)
  : Int
  := sorry

infix:70 " *ℤ " => multInt

inductive Rational where

inductive RationalEq : Rational → Rational → Type where
