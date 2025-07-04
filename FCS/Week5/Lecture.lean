import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture


namespace Learn
open Nat
open List

inductive Term where
  | var (s : String)
  | lam (s : String) (t : Term)
  | app (t₁ : Term) (t₂ : Term)
open Term

infix:25 " @ " => app
notation " \\ " x " => " t => lam x t

def idTerm : Term
  := \ "x" => (var "x")
  -- := lam "x" (var "x")

def appTerm : Term
  := ((var "f") @ (var "x")) @ (var "y")

#eval appTerm


-- Works correctly for closed terms only
def substitute
  (x : String)
  (s : Term)
  (t : Term)
  : Term
  := match t with
    | var y => if x == y then s else var y
    | lam y body => if x == y then lam y body else lam y (substitute x s body)
    | app t₁ t₂ => app (substitute x s t₁) (substitute x s t₂)

notation " [ " x " ↦ " s " ] " t => substitute x s t

inductive ClosedUnder : List String → Term → Type where
  | var : (v ∈ vars) → ClosedUnder vars (var v)
  | lam : ClosedUnder (x :: vars) t → ClosedUnder vars (lam x t)
  | app
    : ClosedUnder (vars) t₁
    → ClosedUnder (vars) t₂
    → ClosedUnder vars (app t₁ t₂)

def Closed t := ClosedUnder nil t


inductive Reduce : Term → Term → Type where
  | appLam : Reduce (app (lam x t) u) ([x ↦ u] t)
  | congAppL : Reduce t t' → Reduce (app t u) (app t' u)
  | congAppR : Reduce u u' → Reduce (app t u) (app t u')
  | congLam : Reduce t t' → Reduce (lam x t) (lam x t')

infix:10 " ⇝ " => Reduce

def redExample
  : (\ "x" => var "x") @ var "a" ⇝ var "a"
  := .appLam


inductive ReduceRTC : Term → Term → Type where
  | refl : ReduceRTC t t
  | trans : (t ⇝ u) → ReduceRTC u s → ReduceRTC t s

infix:10 " ⇝* " => ReduceRTC

def redRtcExample
  : ((\ "x" => (\ "y" => var "x")) @ var "a") @ var "b" ⇝* var "a"
  := .trans (.congAppL .appLam) (.trans .appLam .refl)


def substituteIsClosed
  (closedT : ClosedUnder (x :: xs) t)
  (closedU : ClosedUnder xs u)
  : ClosedUnder xs ([x ↦ u]t)
  := sorry

def reductionIsClosedGeneric
  (red : t ⇝ u)
  (closed : ClosedUnder xs t)
  : ClosedUnder xs u
  := match red with
    | @Reduce.appLam x t u => match closed with
      | .app closedLam closedU => match closedLam with
        | .lam closedT => substituteIsClosed closedT closedU
    | .congAppL r => match closed with
      | .app closedT closedU => .app (reductionIsClosedGeneric r closedT) closedU
    | .congAppR r => match closed with
      | .app closedT closedU => .app closedT (reductionIsClosedGeneric r closedU)
    | .congLam r => match closed with
      | .lam closedBody => .lam (reductionIsClosedGeneric r closedBody)


def reductionIsClosed
  (red : t ⇝ u)
  (closed : Closed t)
  : Closed u
  := reductionIsClosedGeneric red closed


def rename
  (x a : String)
  (t : Term)
  : Term
  := [x ↦ var a]t


inductive AlphaEq : Term → Term → Type where
  | var : AlphaEq (var x) (var x)
  | lam : AlphaEq t₁ (rename y x t₂) → AlphaEq (lam x t₁) (lam y t₂)
  | app : AlphaEq t₁ t₂ → AlphaEq u₁ u₂ → AlphaEq (app t₁ t₂) (app u₁ u₂)

infix:10 " ≃α " => AlphaEq

def alphaExample1
  : (\ "x" => var "x") ≃α (\ "y" => var "y")
  := .lam .var

def alphaExample2
  : (\ "x" => \ "y" => var "x") ≃α (\ "a" => \ "b" => var "a")
  := .lam (.lam .var)


inductive Value : Term → Type where
  | lam : Value (lam x t)

inductive CallByValue : Term → Term → Type where
  | appLam : Value u → CallByValue (app (lam x t) u) ([x ↦ u]t)
  | congAppL : CallByValue t t' → CallByValue (app t u) (app t' u)
  | congAppR : Value t → CallByValue u u' → CallByValue (app t u) (app t u')

infix:10 " ⇒ " => CallByValue

def valueNotReducible
  (val : Value t)
  : ¬(t ⇒ t')
  := λ red => match val with
    | .lam => by contradiction

def deterministic
  (red1 : t ⇒ u)
  (red2 : t ⇒ s)
  : u ≡ s
  := match red1 with
    | .appLam valU => match red2 with
      | .appLam _ => rfl
      | .congAppL redT => by contradiction
      | .congAppR val redU => absurd (valueNotReducible valU redU)
    | .congAppL red1 => match red2 with
      | .appLam _ => by contradiction
      | @CallByValue.congAppL _ _ u red2 => Eq.cong (λ v => v @ u) (deterministic red1 red2)
      | .congAppR val red2 => absurd (valueNotReducible val red1)
    | .congAppR val redU => match red2 with
      | .appLam valU => absurd (valueNotReducible valU redU)
      | .congAppL red => absurd (valueNotReducible val red)
      | .congAppR _ redU2 => Eq.cong _ (deterministic redU redU2)
