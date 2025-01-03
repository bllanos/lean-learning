-- # Examples

-- ## Checking for `none`: Don't repeat yourself

def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird2 (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun x =>
    andThen xs[2]? fun y =>
      some (x, y)

-- ## Infix operators

infixl:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

-- ## Propagating error messages

inductive Except2 (ε : Type) (α : Type) where
  | error : ε → Except2 ε α
  | ok : α → Except2 ε α
deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 2

#eval get ediblePlants 4

def first2 (xs : List α) : Except String α :=
  get xs 0

def firstThird3 (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)

def andThen2 (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

def firstThird4 (xs : List α) : Except String (α × α) :=
  andThen2 (get xs 0) fun result =>
  andThen2 (get xs 2) fun result2 =>
  Except.ok (result, result2)

def ok (x : α) : Except ε α := Except.ok x

def fail (err : ε) : Except ε α := Except.error err

def get2 (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x

infixl:55 " ~~> " => andThen2

def firstThird5 (xs : List α) : Except String (α × α) :=
  get2 xs 0 ~~> fun first =>
  get2 xs 2 ~~> fun third =>
  ok (first, third)

-- ## Logging

def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

def sumAndFindEvens2 : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThen3 (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let { log := thisOut, val := thisRes } := result
  let { log := nextOut, val := nextRes } := next thisRes
  { log := thisOut ++ nextOut, val := nextRes }

def ok2 (x : β) : WithLog α β := { log := [], val := x }

def save (data : α) : WithLog α Unit :=
  { log := [data], val := () }

def sumAndFindEvens3 : List Int → WithLog Int Int
  | [] => ok2 0
  | i :: is =>
    andThen3 (if isEven i then save i else ok2 ()) fun () =>
    andThen3 (sumAndFindEvens3 is) fun sum =>
    ok2 (i + sum)

def inorderSum2 : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok2 0
  | BinTree.branch l x r =>
    andThen3 (inorderSum2 l) fun leftSum =>
    andThen3 (save x) fun () =>
    andThen3 (inorderSum2 r) fun rightSum =>
    ok2 (leftSum + x + rightSum)

infixl:55 " ~~> " => andThen3

def sumAndFindEvens4 : List Int → WithLog Int Int
  | [] => ok2 0
  | i :: is =>
    (if isEven i then save i else ok2 ()) ~~> fun () =>
    sumAndFindEvens4 is ~~> fun sum =>
    ok2 (i + sum)

def inorderSum3 : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok2 0
  | BinTree.branch l x r =>
    inorderSum3 l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum3 r ~~> fun rightSum =>
    ok2 (leftSum + x + rightSum)

-- ## Numbering tree nodes

open BinTree in
def aTree :=
  branch
    (branch
      (branch leaf "a" (branch leaf "b" leaf))
      "c"
      leaf)
    "d"
    (branch leaf "e" leaf)

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok3 (x : α) : State σ α :=
  fun s => (s, x)

def get3 : State σ σ :=
  fun s => (s, s)

def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def andThen4 (first : State σ α) (next : α → State σ β) : State σ β := fun s =>
  let (s', x) := first s
  (next x) s'

infixl:55 " ~~> " => andThen4

def number2 (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α -> State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok3 BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get3 ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok3 (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
