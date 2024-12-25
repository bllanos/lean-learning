-- # Examples

class Monad2 (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β

instance : Monad2 Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad2 (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

#eval firstThirdFifthSeventh getOrExcept slowMammals
#eval firstThirdFifthSeventh getOrExcept fastBirds

-- ## General monad operations

def mapM2 [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM2 f xs >>= fun tl =>
    pure (hd :: tl)

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def getState : State σ σ :=
  fun s => (s, s)

def setState (s : σ) : State σ Unit :=
  fun _ => (s, ())

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  getState >>= fun i =>
  setState (i + howMuch) >>= fun () =>
  pure i

#eval mapM2 increment [1, 2, 3, 4, 5] 0
#eval mapM2 increment [] 21 -- `(21, [])`
-- def mapM2 increment [] 21
--   | [] => pure []
--
-- def mapM2 increment [] 21
--   21 => (21, [])
#eval mapM2 increment [1] 21 -- `(22, [21])`
-- def mapM2 increment [1] 21
--   | 1 :: [] =>
--     increment 1 >>= fun hd =>
--     mapM2 increment [] >>= fun tl =>
--     pure (hd :: tl)
--
-- def mapM2 increment [1] 21
--   increment 1 >>= fun hd =>
--   (fun s => (s, [])) >>= fun [] =>
--   pure (hd :: [])
--
-- def increment 1 a
--   (fun a => (a, a)) >>= fun a =>
--   setState (a + 1) >>= fun () =>
--   pure a
--
-- def increment 1 a
--   (a + 1, a)
--
-- def mapM2 increment [1] 21
--   (fun a => (a + 1, a)) >>= fun hd =>
--   (fun s => (s, [])) >>= fun [] =>
--   pure (hd :: [])
--
-- def mapM2 increment [1] 21
--   (22, 21) >>= fun 21 =>
--   (fun s => (s, [])) >>= fun [] =>
--   pure (21 :: [])
--
-- def mapM2 increment [1] 21
--   (22, 21) >>= fun 21 =>
--   (22, []) >>= fun [] =>
--   pure (21 :: [])
--
-- def mapM2 increment [1] 21
--   (22, [21])
#eval mapM2 increment [1, 2] 21 -- `(24, [21, 22])`

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def save (data : α) : WithLog α Unit :=
  { log := [data], val := () }

instance : Monad (WithLog logged) where
  pure x := { log := [], val := x }
  bind result next :=
    let { log := resultLog, val := resultVal } := result
    let { log := nextLog, val := nextVal } := next resultVal
    { log := resultLog ++ nextLog, val := nextVal }

def isEven (i : Int) : Bool :=
  i % 2 == 0

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i

#eval mapM2 saveIfEven [1, 2, 3, 4, 5]

-- ## The identity monad

def Id2 (t : Type) : Type := t

instance : Monad Id2 where
  pure x := x
  bind x f := f x

#eval mapM2 (m := Id) (· + 1) [1, 2, 3, 4, 5]
#eval mapM2 (fun x => ((x + 1) : Id Nat)) [1, 2, 3, 4, 5]
#eval mapM2 (fun x => (pure (x + 1))) [1, 2, 3, 4, 5]
#eval mapM2 (fun x => (x + 1 : Id Nat)) ([1, 2, 3, 4, 5] : List Nat)

-- ## The monad contract

-- pure v >>= f = f v
-- v >>= pure = v

-- (v >>= f) >>= g = v >>= (fun x => f x >>= g)

-- # Exercises

-- ## Mapping on a tree

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r =>
    f x >>= fun xMap =>
    (mapM f l) >>= fun lMap =>
    (mapM f r) >>= fun rMap =>
    pure (BinTree.branch lMap xMap rMap)

def saveAllAndAdd1 (i : Nat) : WithLog Nat Nat :=
  save i >>= fun () =>
  pure (i + 1)

#eval (BinTree.leaf).mapM saveAllAndAdd1

def t1 := BinTree.branch BinTree.leaf 0 BinTree.leaf

#eval t1.mapM saveAllAndAdd1

def t2 := BinTree.branch
  (BinTree.branch BinTree.leaf 1 (BinTree.branch BinTree.leaf 2 BinTree.leaf))
  0
  (BinTree.branch (BinTree.branch BinTree.leaf 4 BinTree.leaf) 3 BinTree.leaf)

#eval t2.mapM saveAllAndAdd1

-- ## The Option monad contract

-- pure v >>= f = f v
-- Proof:
-- some x >>= f
-- f x

-- v >>= pure = v
-- Proof:
-- v >>= some
-- match v with
-- | some x => some x
-- | none => none
-- v

-- (v >>= f) >>= g = v >>= (fun x => f x >>= g)
-- Proof:
-- (v >>= f) >>= g
-- (match v with
-- | some x => f x
-- | none => none) >>= g
--
-- match v with
-- | some x => match f x with
--   | some y => g y
--   | none => none
-- | none => none
--
-- v >>= (fun x => f x >>= g)
-- match v with
-- | some x => (fun x => f x >>= g) x
-- | none => none
--
-- match v with
-- | some x => (f x >>= g)
-- | none => none
--
-- match v with
-- | some x => match f x with
--   | some y => g y
--   | none => none
-- | none => none

instance : Monad Option where
  pure x := some x
  bind _opt _next := none
-- pure v >>= f = f v
-- some x >>= f
-- none ≠ f x
