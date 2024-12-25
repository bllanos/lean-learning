-- # Examples

-- `do E` = `E`, where `E` is an expression.

-- ```
-- do let x ← E1
--   Stmt
--   ...
--   En
-- ```
-- is
-- ```
-- E1 >>= fun x =>
-- do Stmt
--     ...
--     En
-- ```

-- ```
-- do E1
--   Stmt
--   ...
--   En
-- ```
-- is
-- ```
-- E1 >>= fun () =>
-- do Stmt
--     ...
--     En
-- ```

-- ```
-- do let x := E1
--   Stmt
--   ...
--   En
-- ```
-- is
-- ```
-- let x := E1
-- do Stmt
--     ...
--     En
-- ```

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def firstThirdFifthSeventh2 [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  do
    let first ← lookup xs 0
    let third ← lookup xs 2
    let fifth ← lookup xs 4
    let seventh ← lookup xs 6
    pure (first, third, fifth, seventh)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

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

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← getState
      setState (n + 1)
      let numberedRight ← helper right
      pure (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)

def mapM2 [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM2 f xs))

def increment : State Nat Nat := do
  let n ← getState
  setState (n + 1)
  pure n

def number2 (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure (BinTree.branch (← helper left) ((← increment), x) (← helper right))
  (helper t 0).snd

-- # Exercises

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

def readExcept : ReaderExcept ε ρ ρ := fun env => Except.ok env

def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α := fun _ => Except.ok x

def ReaderExcept.fail (error : ε) : ReaderExcept ε ρ α := fun _ => Except.error error

def ReaderExcept.bind (result : ReaderExcept ε ρ α) (next : α → ReaderExcept ε ρ β) : ReaderExcept ε ρ β :=
  fun env => match result env with
    | Except.ok x => next x env
    | Except.error e => Except.error e

 instance : Monad (ReaderExcept ε ρ) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

abbrev Env : Type := List (String × (Int → Int → Int))

def applyPrimReaderExcept (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int := do
  let env ← readExcept
  match env.lookup op with
  | none => ReaderExcept.fail s!"operator {op} not found"
  | some f => pure (f x y)

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do
    let v1 ← evaluateM applySpecial e1
    let v2 ← evaluateM applySpecial e2
    applyPrim applySpecial p v1 v2

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

open Expr Prim in
#eval evaluateM applyPrimReaderExcept (prim (other "mix") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

def firstThirdFifthSeventh3 [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  do
    pure ((← lookup xs 0), (← lookup xs 2), (← lookup xs 4), (← lookup xs 6))
