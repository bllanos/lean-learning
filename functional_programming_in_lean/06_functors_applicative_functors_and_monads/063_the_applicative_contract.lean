-- # Examples

instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()

-- The Applicative contract for Option

-- some id <*> v = v
-- id <$> v = v
-- v = v

-- some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)

-- some f <*> some x = some (f x)
-- f <$> some x = some (f x)
-- some (f x) = some (f x)

-- u <*> some x = some (fun f => f x) <*> u
-- Assume u = some f
-- some f <*> some x = some (fun f => f x) <*> some f
-- some (f x) = some (f x)

-- ## All applicatives are functors

def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

-- Since:
-- <*> preserves identity
-- <*> preserves composition

class Applicative2 (f : Type → Type) extends Functor f where
  pure : α → f α
  seq: f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)

-- ## All monads are applicative functors

def seq2 [Monad m] (f : m (α → β)) (x : Unit → m α) : m β :=
  x () >>= fun a =>
    f >>= fun f' =>
      pure (f' a)

def seq3 [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  -- The order of these two statements is incorrect.
  -- Would it violate one of the clauses of the Applicative contract?
  let a ← x ()
  let f' ← f
  pure (f' a)

def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)

class Monad2 (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)

-- ## Additional stipulations

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys : (NonEmptyList α) :=
    { head := xs.head, tail := xs.tail ++ (List.cons ys.head ys.tail) }

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
