import FCS.Week1.Lecture
import FCS.Week2.Lecture
import FCS.Week3.Lecture

namespace Learn
open Nat

inductive List (A : Type) where
  | nil
  | cons (head : A) (tail : List A)
open List

infixr:25 (priority := high) " :: " => List.cons

def oneTwoThree1
  : List Nat
  := .cons 1 (.cons 2 (.cons 3 .nil))

def oneTwoThree2
  : List Nat
  := 1 :: 2 :: 3 :: .nil

def length
  (l : List A)
  : Nat
  := match l with
  | .nil => zero
  | .cons _ tail => succ (length tail)

def append
  (l₁ l₂ : List A)
  : List A
  := match l₁ with
  | .nil => l₂
  | .cons head tail => .cons head (append tail l₂)

infix:30 (priority := high) " ++ " => append

def appendExample
  : (1 :: 2 :: 3 :: .nil) ++ (4 :: 5 :: .nil) ≡ 1 :: 2 :: 3 :: 4 :: 5 :: .nil
  := (1 :: 2 :: 3 :: .nil) ++ (4 :: 5 :: .nil)
    ≣ 1 :: ((2 :: 3 :: .nil) ++ (4 :: 5 :: .nil))
    ≣ 1 :: (2 :: ((3 :: .nil) ++ (4 :: 5 :: .nil)))
    ≣ 1 :: (2 :: (3 :: (.nil ++ (4 :: 5 :: .nil))))
    ≣ 1 :: (2 :: (3 :: (4 :: 5 :: .nil)))
    qed

def map
  (f : A → B)
  (lst : List A)
  : List B
  := match lst with
    | .nil => .nil
    | .cons head tail => .cons (f head) (map f tail)

def plusOne
  (n : Nat)
  : Nat
  := n +ℕ 1

#eval map plusOne (1 :: 2 :: 3 :: nil)

def filter
  (f : A → Bool)
  (lst : List A)
  : List A
  := match lst with
    | .nil => .nil
    | .cons head tail =>
      if f head
      then .cons head (filter f tail)
      else filter f tail


-- PRACTICE

def zip
  (l₁ : List A)
  (l₂ : List B)
  : List (A ∧ B)
  := sorry

def zipWith
  (f : A → B → C)
  (l₁ : List A)
  (l₂ : List B)
  : List C
  := sorry

def min
  (n m : Nat)
  : Nat
  := sorry

def max
  (n m : Nat)
  : Nat
  := sorry

-- clip 2 4 (1 :: 2 :: 3 :: 4 :: 5 :: nil) = (2 :: 2 :: 3 :: 4 :: 4 :: nil)
def clip
  (lower upper : Nat)
  (nats : List Nat)
  : List Nat
  := sorry

def flatten
  (lists : List (List A))
  : List A
  := sorry

-- take first n elements of a list (or all if it has less than n elements)
def take
  (n : Nat)
  (lst : List A)
  : List A
  := sorry

-- drop first n elements of a list (or all if it has less than n elements)
def drop
  (n : Nat)
  (lst : List A)
  : List A
  := sorry

-- drop every kth element
-- Hint: you may need a helper function
def dropEveryKth
  (k : Nat)
  (lst : List A)
  : List A
  := sorry


-- LENGTH AND APPEND PROPERTIES

def lengthOfNil
  {A : Type}
  : length (.nil : List A) ≡ 0
  := rfl

def lengthOfCons
  : (length (head :: tail) ≡ succ (length tail))
  := rfl

def lengthOfAppend
  : length (append l₁ l₂) ≡ length l₁ +ℕ length l₂
  := match l₁ with
  | .nil => rfl
  | .cons head tail =>
      length (append (List.cons head tail) l₂)
      ≣ length (List.cons head (append tail l₂))
      ≣ succ (length (append tail l₂))
      ≣⟨ Eq.cong succ lengthOfAppend ⟩ succ (length tail +ℕ length l₂)
      ≣ succ (length tail) +ℕ length l₂
      ≣ length (List.cons head tail) +ℕ length l₂
      qed

def lengthOfMap
  : length (map f lst) ≡ length lst
  := match lst with
    | .nil => rfl
    | .cons head tail =>
        length (map f (.cons head tail))
        ≣ length (.cons (f head) (map f tail))
        ≣ succ (length (map f tail))
        ≣⟨ Eq.cong succ lengthOfMap ⟩ succ (length tail)
        ≣ length (.cons head tail)
        qed

def appendCons
  : (head :: tail) ++ lst ≡ head :: (append tail lst)
  := rfl

def appendNilLeft
  : nil ++ lst ≡ lst
  := rfl

-- SELF
def appendNilRight
  : lst ++ nil ≡ lst
  := sorry

def appendTrans
  -- : append (append l₁ l₂) l₃ ≡ append l₁ (append l₂ l₃)
  : (l₁ ++ l₂) ++ l₃ ≡ l₁ ++ (l₂ ++ l₃)
  := match l₁ with
    | .nil => rfl
    | head :: tail =>
        ((head :: tail) ++ l₂) ++ l₃
        ≣ (head :: (tail ++ l₂)) ++ l₃
        ≣⟨ appendCons ⟩ head :: ((tail ++ l₂) ++ l₃)
        -- ≣⟨ Eq.cong (λ v => head :: v) appendTrans ⟩ head :: (tail ++ (l₂ ++ l₃))
        ≣⟨ Eq.cong _ appendTrans ⟩ head :: (tail ++ (l₂ ++ l₃))
        ≣ (head :: tail) ++ (l₂ ++ l₃)
        qed


-- MEM

inductive Mem : A → List A → Type where
  | memHead : Mem x (.cons x tail)
  | memTail : Mem x tail → Mem x (.cons y tail)

infix:50 (priority := high) " ∈ " => Mem

def oneInOneTwoThree
  : 1 ∈ oneTwoThree2
  := .memHead

def twoInOneTwoThree
  : 2 ∈ oneTwoThree2
  := .memTail .memHead

-- SELF
def threeInOneTwoThree
  : 3 ∈ oneTwoThree2
  := sorry

-- SELF
def memAppendLeft
  (mem : x ∈ l₁)
  : x ∈ append l₁ l₂
  := sorry

-- SELF
def memAppendRight
  (mem : x ∈ l₂)
  : x ∈ append l₁ l₂
  := sorry

def nilIsEmpty
  : ¬(x ∈ nil)
  := λ mem => by contradiction

-- REVERSE

def reverse
  (lst : List A)
  : List A
  := match lst with
    | nil => nil
    | head :: tail => reverse tail ++ (head :: nil)

def reverseDistribute
  : reverse (xs ++ ys) ≡ (reverse ys) ++ (reverse xs)
  := match xs with
    | nil =>
        reverse (nil ++ ys)
        ≣ reverse ys
        ≣⟨ Eq.symm appendNilRight ⟩ reverse ys ++ nil
        ≣ reverse ys ++ reverse nil
        qed
    | head :: tail =>
        reverse ((head :: tail) ++ ys)
        ≣ reverse (head :: (tail ++ ys))
        ≣ (reverse (tail ++ ys)) ++ (head :: nil)
        ≣⟨ Eq.cong (λ v => v ++ (head :: nil)) reverseDistribute ⟩ ((reverse ys) ++ (reverse tail)) ++ (head :: nil)
        ≣⟨ appendTrans ⟩ (reverse ys) ++ ((reverse tail) ++ (head :: nil))
        ≣ (reverse ys) ++ (reverse (head :: tail))
        qed

def shunt
  (xs ys : List A)
  : List A
  := match xs with
    | nil => ys
    | head :: tail => shunt tail (head :: ys)

def shuntToReverse
  : shunt xs ys ≡ reverse xs ++ ys
  := match xs with
    | nil => rfl
    | head :: tail =>
        shunt (head :: tail) ys
        ≣ shunt tail (head :: ys)
        ≣⟨ shuntToReverse ⟩ reverse tail ++ (head :: ys)
        ≣ reverse tail ++ ((head :: nil) ++ ys)
        ≣⟨ Eq.symm appendTrans ⟩ (reverse tail ++ (head :: nil)) ++ ys
        ≣ (reverse (head :: tail)) ++ ys
        qed


def fastReverse
  (xs : List A)
  : List A
  := shunt xs nil

-- SELF
def reversesEq
  : fastReverse xs ≡ reverse xs
  := sorry


-- MAP

def compose
  (f : B → C)
  (g : A → B)
  : A → C
  := λ a => f (g a)

infixr:60 (priority := high) " ∘ " => compose

#eval (succ ∘ succ) 0

def mapCompose
  : map f (map g xs) ≡ map (f ∘ g) xs
  := match xs with
    | nil => rfl
    | head :: tail =>
        map f (map g (head :: tail))
        ≣ map f (g head :: map g tail)
        ≣ f (g head) :: map f (map g tail)
        ≣ (f ∘ g) head :: map f (map g tail)
        ≣⟨ Eq.cong _ mapCompose ⟩ (f ∘ g) head :: map (f ∘ g) tail
        qed

-- SELF
def mapDistribute
  : map f (xs ++ ys) ≡ map f xs ++ map f ys
  := sorry


-- ANY and ALL

inductive All : (A → Type) → List A → Type where
  | allNil : All P nil
  | allCons : P head → All P tail → All P (head :: tail)

inductive NotZero : Nat → Type where
  | notZero : NotZero (succ n)

def allExample
  : All NotZero (1 :: 2 :: 3 :: nil)
  := .allCons .notZero (.allCons .notZero (.allCons .notZero .allNil))

inductive Any : (A → Type) → List A → Type where
  | anyHead : P head → Any P (head :: tail)
  | anyTail : Any P tail → Any P (head :: tail)

def anyExample
  : Any NotZero (0 :: 2 :: 0 :: nil)
  -- := .anyHead .notZero -- Will fail!
  := .anyTail (.anyHead .notZero)

/-
Does not work for arbitrary lists!!

def AllImpliesAny
  (all : All P lst)
  : Any P lst
  := match lst with
    | nil => _
    | head :: tail => _
-/


-- SELF
def AllImpliesAny
  (all : All P (head :: tail))
  : Any P (head :: tail)
  := sorry

def anyImpliesExists
  (any : Any P lst)
  : ∃ x, x ∈ lst ∧ P x
  := match any with
    | @Any.anyHead _ _ head tail pHead => .exists head (And.mk .memHead pHead)
    | @Any.anyTail _ _ tail head pInTail => match anyImpliesExists pInTail with
      -- | .exists x memAndPx => .exists x (And.mk (.memTail memAndPx.first) memAndPx.second)
      | .exists x { first := mem, second := px } => .exists x (And.mk (.memTail mem) px)

def allImpliesForAll
  (all : All P lst)
  : ∀ x, x ∈ lst → P x
  := match all with
    | .allNil => λ _ mem => absurd (nilIsEmpty mem)
    | .allCons pHead allTail => λ x mem => match mem with
      | .memHead => pHead
      | .memTail memTail => allImpliesForAll allTail x memTail

def allAppend
  (all₁ : All P l₁)
  (all₂ : All P l₂)
  : All P (l₁ ++ l₂)
  := match l₁ with
    | nil => all₂
    | _ :: _ => match all₁ with
      | .allCons pHead allTail => .allCons pHead (allAppend allTail all₂)

def allGetHead
  (all : All P (head :: tail))
  : P head
  := match all with
    | .allCons pHead _ => pHead

def allGetTail
  (all : All P (head :: tail))
  : All P tail
  := match all with
    | .allCons _ allTail => allTail

def allReverse
  (all : All P xs)
  : All P (reverse xs)
  := match xs with
    | nil => .allNil
    -- All P (reverse (head :: tail))
    -- All P ((reverse tail) ++ (head :: nil))
    | _head :: _tail => match all with
      | .allCons pHead allTail =>
          allAppend (allReverse allTail) (.allCons pHead .allNil)
