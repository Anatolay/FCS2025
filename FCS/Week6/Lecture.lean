import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture
import FCS.Week4.Lecture


namespace Learn
open Nat
open List

-- TYPES
inductive Typ where
  | BoolTyp
  | NatTyp
  | Arr (A B : Typ)
open Typ


-- TERMS
inductive Term where
  | tru
  | fls
  | iff (t₁ t₂ t₃ : Term)
  | z
  | suc (t : Term)
  | pred (t : Term)
  | iszero (t : Term)
  | var (s : String)
  | lam (v : String) (A : Typ) (t : Term)
  | app (t₁ t₂ : Term)
open Term


-- VALUES
inductive NumericValue : Term → Type where
  | z : NumericValue z
  | suc : NumericValue n → NumericValue (suc n)

inductive Value : Term → Type where
  | tru : Value tru
  | fls : Value fls
  | nv : NumericValue n → Value n
  | lam : Value (lam x A t)


-- Works correctly for closed terms only
def substitute
  (x : String)
  (s : Term)
  (t : Term)
  : Term
  := match t with
    -- Booleans
    | tru => tru
    | fls => fls
    | iff t₁ t₂ t₃ => iff (substitute x s t₁) (substitute x s t₂) (substitute x s t₃)
    -- Numeric
    | z => z
    | suc t => suc (substitute x s t)
    | pred t => pred (substitute x s t)
    | iszero t => iszero (substitute x s t)
    -- Lam
    | var y => if x == y then s else var y
    | lam y A body => if x == y then lam y A body else lam y A (substitute x s body)
    | app t₁ t₂ => app (substitute x s t₁) (substitute x s t₂)

notation " [ " x " ↦ " s " ] " t => substitute x s t


-- REDUCTION
inductive Reduce : Term → Term → Type where
  -- Booleans
  | ifTru : Reduce (iff tru t₂ t₃) t₂
  | ifFls : Reduce (iff fls t₂ t₃) t₃
  | ifCong : Reduce t₁ u₁ → Reduce (iff t₁ t₂ t₃) (iff u₁ t₂ t₃)
  -- Numeric
  | sucCong : Reduce t u → Reduce (suc t) (suc u)
  | predCong : Reduce t u → Reduce (pred t) (pred u)
  | iszeroCong : Reduce t u → Reduce (iszero t) (iszero u)
  | iszeroZero : Reduce (iszero z) tru
  | iszeroSuc : Reduce (iszero (suc t)) fls
  | predZero : Reduce (pred z) z
  | predSuc : Reduce (pred (suc t)) t
  -- Lam
  | appCongL {t t' u} : Reduce t t' → Reduce (app t u) (app t' u)
  | appCongR {t u u'} : Value t → Reduce u u' → Reduce (app t u) (app t u')
  | lamApp {A v x t} : Value v → Reduce (app (lam x A t) v) ([x ↦ v]t)

infix:20 " ⇝ " => Reduce


-- CONTEXT
def Ctx := List (String ∧ Typ)

-- x : A ∈ Γ, but the first occurence only
inductive Lookup : String → Typ → Ctx → Type where
  | here : Lookup x A (⟨x, A⟩ :: tail)
  | there
    : ¬(x ≡ y)
    → Lookup x A tail
    → Lookup x A (⟨y, B⟩ :: tail)

-- \vdots for ⋮, \ni for ∋
notation (priority := high) Γ " ∋ " x " ⋮ " A => Lookup x A Γ

-- TYPING RELATION
inductive HasType : Ctx → Term → Typ → Type where
  -- Booleans
  | tru : HasType Γ tru BoolTyp
  | fls : HasType Γ fls BoolTyp
  | iff {Γ T t₁ t₂ t₃}
    : HasType Γ t₁ BoolTyp
    → HasType Γ t₂ T
    → HasType Γ t₃ T
    → HasType Γ (iff t₁ t₂ t₃) T
  -- Numeric
  | z : HasType Γ z NatTyp
  | suc
    : HasType Γ t NatTyp
    → HasType Γ (suc t) NatTyp
  | pred
    : HasType Γ t NatTyp
    → HasType Γ (pred t) NatTyp
  | iszero
    : HasType Γ t NatTyp
    → HasType Γ (iszero t) BoolTyp
  -- Lam
  | var
    : (Γ ∋ x ⋮ A)
    → HasType Γ (var x) A
  | lam {Γ A B x t}
    : HasType (⟨x, A⟩ :: Γ) t B
    → HasType Γ (lam x A t) (Arr A B)
  | app {Γ A B t₁ t₂}
    : HasType Γ t₁ (Arr A B)
    → HasType Γ t₂ A
    → HasType Γ (app t₁ t₂) B

-- \vdash for ⊢
notation Γ " ⊢ " t " ⋮ " A => HasType Γ t A


-- EXERCISES

-- λx:Bool. 0
def ex1
  : nil ⊢ lam "x" .BoolTyp z ⋮ .Arr .BoolTyp .NatTyp
  := sorry

-- if false then (λx:Nat.x) else (λx:Nat.0)
def ex2
  : nil ⊢ iff fls (lam "x" .NatTyp (var "x")) (lam "x" .NatTyp z) ⋮ .Arr .NatTyp .NatTyp
  := sorry

-- (λx:Bool.0) (iszero 0)
def ex3
  : nil ⊢ app (lam "x" .BoolTyp z) (iszero z) ⋮ .NatTyp
  := sorry

-- (λn:Nat.iszero n) (succ 0)
def ex4
  : nil ⊢ app (lam "n" .NatTyp (iszero (var "n"))) (suc z) ⋮ .BoolTyp
  := sorry

-- λb:Bool. if b then false else b
def ex5
  : nil ⊢ lam "b" .BoolTyp (iff (var "b") fls (var "b")) ⋮ .Arr .BoolTyp .BoolTyp
  := sorry


-- PROPERTIES

-- 1. uniqueness of typing derivations

def lookupUnique
  (lookup₁ : Γ ∋ x ⋮ A)
  (lookup₂ : Γ ∋ x ⋮ B)
  : A ≡ B
  := match lookup₁ with
    | .here => match lookup₂ with
      | .here => rfl
      | .there neq _ => absurd (neq rfl)
    | .there neq inTail₁ => match lookup₂ with
      | .here => absurd (neq rfl)
      | .there _ inTail₂ => lookupUnique inTail₁ inTail₂

def uniqueType
  (typ1 : Γ ⊢ t ⋮ A)
  (typ2 : Γ ⊢ t ⋮ B)
  : A ≡ B
  := match t with
    | tru => match typ1, typ2 with | .tru, .tru => rfl
    | fls => match typ1, typ2 with | .fls, .fls => rfl
    | iff t₁ t₂ t₃ => match typ1, typ2 with
      | .iff _ t₂A _, .iff _ t₂B _ => uniqueType t₂A t₂B
    | z => match typ1, typ2 with | .z, .z => rfl
    | suc t => match typ1, typ2 with | .suc _, .suc _ => rfl
    | pred t => match typ1, typ2 with | .pred _, .pred _ => rfl
    | iszero t => match typ1, typ2 with | .iszero _, .iszero _ => rfl
    | var s => match typ1, typ2 with
      | .var lookup₁, .var lookup₂ => lookupUnique lookup₁ lookup₂
    | lam v A t => match typ1, typ2 with
      | .lam bodyTyp₁, .lam bodyTyp₂ => Eq.cong _ (uniqueType bodyTyp₁ bodyTyp₂)
    | app t₁ t₂ => match typ1, typ2 with
      | .app _ _, .app _ _ => sorry


-- 2. values are irreducible

def numericValuesNotReduce
  (nv : NumericValue t)
  : ¬(t ⇝ u)
  := match nv with
    | .z => λ zu => by contradiction
    | .suc nv => λ svu => match svu with
      | .sucCong red => (numericValuesNotReduce nv) red

def valuesNotReduce
  (val : Value t)
  : ¬(t ⇝ u)
  := match val with
    | .tru => λ red => by contradiction
    | .fls => λ red => by contradiction
    | .nv nv => numericValuesNotReduce nv
    | .lam => λ red => by contradiction


-- 3. typed values

def natValueIsNumeric
  (wellTyped : nil ⊢ t ⋮ NatTyp)
  (value : Value t)
  : NumericValue t
  := match value with
    | .tru => by contradiction
    | .fls => by contradiction
    | .nv nv => nv
    | .lam => by contradiction

def valueBool
  (wellTyped : nil ⊢ t ⋮ BoolTyp)
  (value : Value t)
  : (t ≡ tru) ∨ (t ≡ fls)
  := match value with
    | .tru => .left rfl
    | .fls => .right rfl
    | .nv nv => match nv with
      | .z => by contradiction
      | .suc _ => by contradiction
    | .lam => by contradiction

def valueFun
  (wellTyped : nil ⊢ t ⋮ Arr A B)
  (value : Value t)
  : ∃ x, ∃ body, t ≡ lam x A body
  := match value with
    | .tru => by contradiction
    | .fls => by contradiction
    | .nv nv => match nv with
      | .z => by contradiction
      | .suc _ => by contradiction
    | .lam => match wellTyped with
      | @HasType.lam _ A _ x t _ => .exists x (.exists t rfl)


-- 4. progress

def progress
  (wellTyped : nil ⊢ t ⋮ T)
  : Value t ∨ ∃ u, t ⇝ u
  := match wellTyped with
    -- Boolean
    | .tru => .left .tru
    | .fls => .left .fls
    | @HasType.iff _ _ t₁ t₂ t₃ t₁Bool t₂A t₃A => match progress t₁Bool with
      | .left t₁Val => match valueBool t₁Bool t₁Val with
        | .left eq => .right (.exists t₂ (Eq.subst (λ v => iff v t₂ t₃ ⇝ t₂) (Eq.symm eq) .ifTru))
        | .right eq => .right (.exists t₃ (Eq.subst (λ v => iff v t₂ t₃ ⇝ t₃) (Eq.symm eq) .ifFls))
      | .right (.exists u t₁u) => .right (.exists (iff u t₂ t₃) (.ifCong t₁u))
    -- Numeric
    | .z => .left (.nv .z)
    | .suc tNat => match progress tNat with
      | .left tVal => .left (.nv (.suc (natValueIsNumeric tNat tVal)))
      | .right (.exists u tu) => .right (.exists (suc u) (.sucCong tu))
    | .pred tNat => match progress tNat with
      | .left tVal => match natValueIsNumeric tNat tVal with
        | .z => .right (.exists z .predZero)
        | .suc n => .right (.exists _ .predSuc)
      | .right (.exists u tu) => .right (.exists (pred u) (.predCong tu))
    | .iszero tNat => match progress tNat with
      | .left tVal => match natValueIsNumeric tNat tVal with
        | .z => .right (.exists tru .iszeroZero)
        | .suc n => .right (.exists fls .iszeroSuc)
      | .right (.exists u tu) => .right (.exists (iszero u) (.iszeroCong tu))
    -- Lam
    | .var _ => by contradiction
    | .lam bodyTyp => .left .lam
    | @HasType.app _ A B t₁ t₂ t₁Typ t₂Typ => match progress t₁Typ with
      | .left t₁Val => match progress t₂Typ with
        | .left t₂Val => match valueFun t₁Typ t₁Val with
          | .exists x (.exists body eq) => .right
              (.exists
                ([x ↦ t₂]body)
                (Eq.subst
                  (λ v => app v t₂ ⇝ [x ↦ t₂]body)
                  (Eq.symm eq)
                  (.lamApp t₂Val)
                )
              )
        | .right (.exists u t₂u) => .right (.exists (app t₁ u) (.appCongR t₁Val t₂u))
      | .right (.exists u t₁u) => .right (.exists (app u t₂) (.appCongL t₁u))
