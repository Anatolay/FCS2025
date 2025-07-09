import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture


namespace Learn
open Nat
open List

inductive DeBruijn where
  | boundVar (n : Nat)
  | freeVar (s : String)
  | lam (body : DeBruijn)
  | app (t₁ t₂ : DeBruijn)
open DeBruijn

def ifEq
  (n m : Nat)
  (t₁ t₂ : A)
  : A
  := match n, m with
    | zero, zero => t₁
    | succ _, zero => t₂
    | zero, succ _ => t₂
    | succ n', succ m' => ifEq n' m' t₁ t₂

def ifLess
  (n m : Nat)
  (t₁ t₂ : A)
  : A
  := match n, m with
    | zero, zero => t₂
    | succ _, zero => t₂
    | zero, succ _ => t₁
    | succ n', succ m' => ifEq n' m' t₁ t₂

def incVars
  (k : Nat)
  (t : DeBruijn)
  : DeBruijn
  := match t with
    | boundVar n => ifLess n k (boundVar n) (boundVar (succ n))
    | freeVar s => freeVar s
    | lam body => lam (incVars (succ k) body)
    | app t₁ t₂ => app (incVars k t₁) (incVars k t₂)

notation " ↑ " t => incVars 0 t


def substitute
  (n : Nat)
  (s : DeBruijn)
  (t : DeBruijn)
  : DeBruijn
  := match t with
    | freeVar y => freeVar y
    | boundVar m => ifLess n m (boundVar (decrementNat m)) (ifEq n m s (boundVar m))
    | lam body => lam (substitute (succ n) ↑s body)
    | app t₁ t₂ => app (substitute n s t₁) (substitute n s t₂)

notation " [ " n " ↦ " s " ] " t => substitute n s t


inductive Reduce : DeBruijn → DeBruijn → Type where
  | appCongL : Reduce t₁ u₁ → Reduce (app t₁ t₂) (app u₁ t₂)
  | appCongR : Reduce t₂ u₂ → Reduce (app t₁ t₂) (app t₁ u₂)
  | lamCong : Reduce t u → Reduce (lam t) (lam u)
  | appLam : Reduce (app (lam body) t) ([0 ↦ t]body)
