namespace Learn

-- Define functions with the `def` keyword
-- Unlike most languages, we do not need `return` statements:
-- the body of the function is already a value to be returned,
-- akin to mathematical "f(x) = x²"
def double(n : Nat): Nat := n * 2

def double'
  (n : Nat)
  : Nat
  := n + n

-- Compute given expression with the `eval` keyword
-- Note that we do not need parenthesis to call functions:
-- `double 5` instead of `double(5)`
#eval double 5

-- Functions are higher-order (can take and return other functions)
def apply
  (n : Nat)
  (f : Nat → Nat)
  : Nat
  := f n

#eval apply 4 double

-- Lambda functions (functions without a name)
def lambdaShowcase
  (n : Nat)
  : Nat
  -- λ ─ declare a nameless function
  -- x ─ name of the argument
  -- => ─ after this simbol we put function body (one large return statement)
  -- similar to Python's `lambda x: x` or JS's `(x) => x`
  := (λ x => x) n

-- Function composition: f ∘ g (x) = f(g(x))
def compose
  (f : Nat → Nat)
  (g : Nat → Nat)
  : Nat → Nat
  := λ x => f (g x)

def max
  (n : Nat)
  (m : Nat)
  : Nat
  := if n > m then n else m

def max'
  (n m : Nat)
  : Nat
  := if n >= m then n else m

#eval max 4 10

-- Lean supports structures (somewhat similar to C struct or JS objects)
structure PairNat where
  fst : Nat
  snd : Nat

-- We can access structure's value with the dot notation
def first
  (p : PairNat)
  : Nat
  := p.fst

-- We can create structures with the object notation ("{" ... "}")
#eval first { fst := 1, snd := 2 }
-- Additionally, Lean creates function `mk` which works similar to
-- Java's default constructor (accepting all fields of the structure)
#eval first (PairNat.mk 1 2)

-- Additionally, we can use field names as functions that retrieve
-- the fields, e.g. `PairNar.fst` retrieves field `fst` of a given `PairNat`
def first'
  (p : PairNat)
  : Nat
  := PairNat.fst p

-- Finally, we can pattern-match on structures, similar to JS ot C's switch
def first''
  (p : PairNat)
  : Nat
  := match p with
  | { fst, snd } => fst

def swap
  (p : PairNat)
  : PairNat
  := match p with
  | { fst, snd } => { fst := snd, snd := fst }

#eval swap { fst := 1, snd := 2 }

def ifThenElseNat
  (b : Bool)
  (n m : Nat)
  : Nat
  := if b then n else m

-- We can pattern match on any value, e.g. on booleans
def ifThenElseNat'
  (b : Bool)
  (n m : Nat)
  : Nat
  := match b with
  | true => n
  | false => m

-- To create a function over some generic types, we need to include
-- the type as a function argument
def ifThenElse
  (α : Type)
  (b : Bool)
  (n m : α)
  : α
  := if b then n else m

#eval ifThenElse PairNat true { fst := 0, snd := 0 } { fst := 5, snd := 5 }
#eval ifThenElse PairNat false { fst := 0, snd := 0 } { fst := 5, snd := 5 }

-- Structures can also be generic, e.g. this pair store two arbitrary values
structure Pair (α : Type) (β : Type) where
  fst : α
  snd : β

def swap'
  (p : Pair α β)
  : Pair β α
  -- := match p with
  -- | { fst, snd } => { fst := snd, snd := fst }
  := Pair.mk p.snd p.fst

-- We can pass generic functions as arguments
def mapFst
  (p : Pair α₁ β)
  (f : α₁ → α₂)
  : Pair α₂ β
  := Pair.mk (f p.fst) p.snd

-- Lean supports enumerations
-- The keyword is `inductive`, you will later learn why
inductive TrafficLight where
  | green
  | yellow
  | red

-- To work with enums, we need to pattern match over them.
-- Similar to C's switch case
def canDrive
  (tl : TrafficLight)
  : Bool
  := match tl with
  | TrafficLight.green => true
  | TrafficLight.yellow => false
  | TrafficLight.red => false

-- We may include a "catch all" pattern
def canDrive'
  (tl : TrafficLight)
  : Bool
  := match tl with
  | TrafficLight.green => true
  | _x => false

-- Enums are not a plain list of alternatives:
-- each variant can have some data attached
inductive CandyBox where
  | Empty
  | NonEmpty (n : Nat)

-- When pattern matching, we also match over the value
-- attached to the given variant
def countCandies
  (box : CandyBox)
  : Nat
  := match box with
  | CandyBox.Empty => 0
  | CandyBox.NonEmpty n => n

#eval countCandies (CandyBox.NonEmpty 5)

inductive OneTwoThree where
  | One (n : Nat)
  | Two (h : Nat) (m : Nat)
  | Three (n : Nat) (m : Nat) (k : Nat)

def sum
  (ott : OneTwoThree)
  : Nat
  := match ott with
  | OneTwoThree.One n => n
  | OneTwoThree.Two n m => n + m
  | OneTwoThree.Three n m k => n + m + k


-- Tasks:

def min
  (n m : Nat)
  : Nat
  := sorry

-- vector addition
def addPair
  (p1 p2 : PairNat)
  : PairNat
  := sorry

-- vector dot product
def dotProdPair
  (p1 p2 : PairNat)
  : Nat
  := sorry

-- Fill-in commented code to get a function to map over both fields of a Pair
def map2
  -- (p : Pair ?? ??)
  -- (f : ??)
  -- (g : ??)
  : Pair α₂ β₂
  := sorry

-- Find the maximum Nat in the given OneTwoThree value
def maxOneTwoThree
  (ott : OneTwoThree)
  : Nat
  := sorry
