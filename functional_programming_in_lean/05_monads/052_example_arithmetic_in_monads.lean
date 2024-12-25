-- # Examples

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 15) (prim minus (const 45) (prim times (const 5) (const 9)))

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)

#eval (5 : Int) / (0 : Int) -- `0`

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateOption2 : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption2 e1 >>= fun v1 =>
    evaluateOption2 e2 >>= fun v2 =>
    applyPrimExcept p v1 v2

#eval evaluateOption2 fourteenDivided

def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2

#eval evaluateM applyPrimOption fourteenDivided
#eval evaluateM applyPrimExcept fourteenDivided

def applyDivOption (x : Int) (y : Int) : Option Int :=
  if y == 0 then
    none
  else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
  if y == 0 then
    Except.error s!"Tried to divide {x} by zero"
  else pure (x / y)

def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM2 [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM2 applyDiv e1 >>= fun v1 =>
    evaluateM2 applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2

-- ## Further effects

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim2 [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM3 [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM3 applySpecial e1 >>= fun v1 =>
    evaluateM3 applySpecial e2 >>= fun v2 =>
    applyPrim2 applySpecial p v1 v2

-- ## No effects

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM3 (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

-- ## Nondeterministic search

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | y :: ys => Many.more y (fun () => Many.fromList ys)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ => Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

-- Many.bind (Many.one v) f
-- Many.more v (fun _ => Many.none), f
-- (f v).union (bind (Many.none) f)
-- (f v).union Many.none
-- Either:
--   Many.none, or
--   Many.more x xs, Many.none => Many.more x (fun () => union (xs ()) Many.none)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

open Expr Prim NeedsSearch

#eval (evaluateM3 applySearch (prim plus (const 1) (prim (other choose) (const 2) (const 5)))).takeAll

#eval (evaluateM3 applySearch (prim plus (const 1) (prim (other div) (const 2) (const 0)))).takeAll

#eval (evaluateM3 applySearch (prim (other div) (const 90) (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll

-- ## Custom environments

def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env

 instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

open Expr Prim in
#eval evaluateM3 applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

-- # Exercises

-- ## Checking contracts

-- ### State σ

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

-- pure v >>= f = f v
--
-- bind (pure v) f
-- fun s => let (s', x) := (s, v) in f x s'
-- fun s => f v s
-- f v

-- v >>= pure = v
--
-- bind v pure
-- fun s => let (s', x) := v s in pure x s'
-- fun s => let (s', x) := v s in (s', x)
-- fun s => v s
-- v

-- (v >>= f) >>= g = v >>= (fun x => f x >>= g)
--
-- (v >>= f) >>= g
-- bind (bind v f) g
-- fun s => let (s', x) := (bind v f) s in g x s'
-- fun s => let (s', x) := (
--     fun s'' => let (s''', x') := v s'' in f x' s'''
--   ) s in g x s'
-- fun s => let (s', x) := (
--     let (s''', x') := v s in f x' s'''
--   ) in g x s'
-- fun s => let (s', x) := (
--     let (s'', x') := v s in f x' s''
--   ) in g x s'
--
-- v >>= (fun x => f x >>= g)
-- fun s => let (s', x) := v s in (fun x' => f x' >>= g) x s'
-- fun s => let (s', x) := v s in (fun x' => fun s'' =>
--       let (s''', x'') := f x' s'' in g x'' s'''
--     ) x s'
-- fun s => let (s', x) := v s in (fun s'' =>
--       let (s''', x'') := f x s'' in g x'' s'''
--     ) s'
-- fun s => let (s', x) := v s in (
--       let (s''', x'') := f x s' in g x'' s'''
--     )

-- ### Except ε

inductive Except2 (ε : Type) (α : Type) where
  | error (e : ε)
  | ok (x : α)

instance : Monad (Except2 ε) where
  pure := Except2.ok
  bind first next :=
    match first with
    | Except2.error e => Except2.error e
    | Except2.ok x => next x

-- pure v >>= f = f v
--
-- ok v => f v

-- v >>= pure = v
--
-- match v with
-- | error e => error e
-- | ok x => ok x

-- (v >>= f) >>= g = v >>= (fun x => f x >>= g)
--
-- (v >>= f) >>= g
--
-- match (match v with
-- | error e => error e
-- | ok x => f x) with
--   | error e => error e
--   | ok y => g y
--
-- match v with
-- | error e => error e
-- | ok x => match f x with
--   | error e => error e
--   | ok y => g y
--
-- v >>= (fun x => f x >>= g)
--
-- match v with
-- | error e => error e
-- | ok x => (fun x' =>
--     match f x' with
--     | error e => error e
--     | ok y => g y) x
--
-- match v with
-- | error e => error e
-- | ok x => match f x with
--     | error e => error e
--     | ok y => g y

-- ### Readers with failure

-- #### Option

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def readOption : ReaderOption ρ ρ := fun env => ↑env

def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => ↑x

def ReaderOption.none : ReaderOption ρ α := fun _ => (Option.none (α := α))

def ReaderOption.bind (result : ReaderOption ρ α) (next : α → ReaderOption ρ β) : ReaderOption ρ β :=
  fun env => match result env with
    | Option.none => Option.none
    | some x => next x env

 instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

def applyPrimReaderOption (op : String) (x : Int) (y : Int) : ReaderOption Env Int :=
  readOption >>= fun env =>
  match env.lookup op with
  | none => ReaderOption.none
  | some f => pure (f x y)

open Expr Prim in
#eval evaluateM3 applyPrimReaderOption (prim (other "mix") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

-- #### Except

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

def applyPrimReaderExcept (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int :=
  readExcept >>= fun env =>
  match env.lookup op with
  | none => ReaderExcept.fail s!"operator {op} not found"
  | some f => pure (f x y)

open Expr Prim in
#eval evaluateM3 applyPrimReaderExcept (prim (other "mix") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

-- ### A tracing evaluator

inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

def save (data : α) : WithLog α Unit :=
  { log := [data], val := () }

instance : Monad (WithLog logged) where
  pure x := { log := [], val := x }
  bind result next :=
    let { log := resultLog, val := resultVal } := result
    let { log := nextLog, val := nextVal } := next resultVal
    { log := resultLog ++ nextLog, val := nextVal }

def applyTraced (op : ToTrace (Prim Empty)) (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  match op with
  | ToTrace.trace Prim.plus => { log := [(Prim.plus, x, y)], val := (x + y) }
  | ToTrace.trace Prim.minus => { log := [(Prim.minus, x, y)], val := (x - y) }
  | ToTrace.trace Prim.times => { log := [(Prim.times, x, y)], val := (x * y) }

deriving instance Repr for Empty
deriving instance Repr for Prim

open Expr Prim ToTrace in
#eval evaluateM3 applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))
