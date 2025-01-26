-- # Examples

structure LetterCounts where
  vowels : Nat := 0
  consonants : Nat := 0
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiouy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)

#eval countLetters (m := M1) "hello" ⟨0, 0⟩
#eval countLetters (m := M2) "hello" ⟨0, 0⟩

#eval countLetters (m := M1) "hello!e" ⟨0, 0⟩
#eval countLetters (m := M2) "hello!e" ⟨0, 0⟩

def countWithFallback
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"

#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩

#eval countWithFallback (m := M1) "hello!e" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello!e" ⟨0, 0⟩

-- ## Commuting monads

-- # Exercises

-- ## ReaderT and StateT

def ReaderT2 (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m α

def StateT2 (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

def ReaderThenState (ρ : Type u) (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → ρ → m (α × σ)

def StateThenReader (ρ : Type u) (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → σ → m (α × σ)

-- ReaderT and StateT commute

-- ## ReaderT and ExceptT

def ExceptT2 (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)

def ReaderThenExcept (ρ : Type u) (ε : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → m (Except ε α)

def ExceptThenReader (ρ : Type u) (ε : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  ρ → (Except ε (m α))

-- ReaderT and ExceptT commute only if ExceptT commutes with `m`

-- ## A ManyT monad transformer

--- ### Many monad

inductive Many (α : Type u) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

def Many.map (f : α → β) : Many α → Many β
  | .none => .none
  | .more x xs =>
    .more (f x) (fun () => (xs ()).map f)

def Many.mapM [Monad m] (f : α → m β) : Many α → m (Many β)
  | .none => pure .none
  | .more x xs =>
    (f x) >>= fun y =>
    Many.mapM f (xs ()) >>= fun ys =>
    pure (.more y (fun () => ys))

def Many.join : Many (Many α) → Many α
  | .none => .none
  | .more x xs =>
    x.union ((xs ()).join)

instance : Functor Many where
  map := Many.map

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

--- ### Many monad transformer

def WithManyT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Many α)

def WithManyT.mk (x : m (Many α)) : WithManyT m α := x
def WithManyT.run (x : WithManyT m α) : m (Many α) := x

#check List.foldlM

-- Version that eagerly evaluates `result`
-- instance {m : Type u → Type v} [Monad m] : Monad (WithManyT m) where
--   pure x := WithManyT.mk (pure (pure x))
--   bind result next := WithManyT.mk (bind result fun inner =>
--     let results : m (List _) := (List.mapM next inner.takeAll)
--     bind results fun x =>
--       let allUnion := List.foldl Many.union Many.none x
--       pure allUnion
--     )

instance {m : Type u → Type v} [Monad m] : Monad (WithManyT m) where
  pure x := WithManyT.mk (pure (pure x))
  bind result next := WithManyT.mk (bind result fun inner =>
    let results : m (Many (Many _)) := (Many.mapM next inner)
    Many.join <$> results)

instance [Monad m] : MonadLift m (WithManyT m) where
  monadLift action := WithManyT.mk (pure <$> action)

-- ### Checking the monad transformer contract

-- (pure v) >>= f = f v
-- Proof:
-- (pure (pure v)) >>= f
-- Many.join <$> (Many.mapM f (pure v))
-- f v

-- v >>= pure = v
-- Proof:
-- v >>= (fun x => pure (pure x))
-- bind v fun inner =>
--   Many.join <$> (Many.mapM (fun x => pure (pure x)) inner)
-- bind v fun inner =>
--   Many.join <$> (pure (Many.one inner))
-- bind v fun inner =>
--   pure inner
-- v

-- (v >>= f) >>= g = v >>= fun x => (f x >>= g)
-- (v >>= f) >>= g is
-- bind (bind v fun seq1 =>
--   Many.join <$> (Many.mapM f seq1)) fun seq2 =>
--   Many.join <$> (Many.mapM g seq2)
-- The result contains the union of all sequences of g on all elements of (f v).
-- Sequences are short-circuited by m, then by f, then by g.
--
-- v >>= fun x => (f x >>= g) is
-- bind v fun seq1 =>
--   Many.join <$> (Many.mapM (fun x => bind (f x) fun seq2 =>
--     Many.join <$> (Many.mapM g seq2)) seq1)
-- The result contains the union of all sequences of g on all elements of (f v).
-- Sequences are short-circuited by m, then by f, then by g.

-- monadLift (pure x) = pure x
-- Proof:
-- pure <$> (pure x)
-- pure (pure x)
-- pure x

-- monadLift (x >>= f) = (monadLift x) >>= fun y => monadLift (f y)
-- Proof:
-- monadLift (x >>= f) is
-- pure <$> (x >>= f)
-- This is, loosely speaking, (m (Many.one (extract (f x))))
--
-- (monadLift x) >>= fun y => monadLift (f y) is
-- bind (pure <$> x) fun inner =>
--   Many.join <$> (Many.mapM (fun y => monadLift (f y)) inner)
-- Inner has exactly one element
-- bind (m x) fun x =>
--   Many.join <$> (monadLift (f x))
-- Apply loose reasoning
-- bind (m x) fun x =>
--   (m (Many.one (extract (f x))))
-- Which is the same as (monadLift (x >>= f))

-- ### Alternative instance

instance : Alternative Many where
  failure := .none
  orElse
    | .none, y => y ()
    | .more x xs, _ => .more x xs

instance [Monad m] [Alternative m] : Alternative (WithManyT m) where
  failure := WithManyT.mk failure
  orElse result next : (WithManyT m _) :=
    let mappedNoneToFailure := ((WithManyT.run result) >>= fun inner =>
        match inner with
        | .none => Alternative.failure
        | success => pure success
      )
    let failover := Alternative.orElse mappedNoneToFailure next
    WithManyT.mk failover

-- ### Behaviour class

class MonadMany (m : Type u → Type v) where
  fromList : {α : Type u} → List α → m α
  -- For this to have the same signature as Many.takeAll,
  -- `m` would need to be a comonad
  takeAll : {α : Type u} → m α → m (List α)

instance : MonadMany Many where
  fromList := Many.fromList
  takeAll x := Many.one x.takeAll

instance [Monad m] : MonadMany (WithManyT m) where
  fromList xs :=
    WithManyT.mk (pure (Many.fromList xs))
  takeAll x := do
    let inner ← (WithManyT.run x)
    pure inner.takeAll

-- ## ManyT and StateT

def WithManyT2 (m : Type u → Type v) (α : Type u) : Type v :=
  m (Many α)

def StateT3 (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

def ManyThenState (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (Many (α × σ))

def StateThenMany (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m ((Many α) × σ)

-- WithManyT and StateT do not commute:
-- `ManyThenState` is useful if a function needs to generate a stream of states,
-- such as if the elements of the stream depend on the state.
-- `StateThenMany` is useful if a function needs to generate a stream
-- and simultaneously return state for generating another stream.

-- ### Behaviour class instances

instance [Monad m] [MonadMany m] : MonadMany (StateT σ m) where
  fromList {α} xs := (MonadMany.fromList xs : m α)
  takeAll x := fun s =>
    let inner := x s
    let taken := MonadMany.takeAll inner
    -- There is no general way to combine the states from all list elements,
    -- so use the first state, if the list is not empty,
    -- or the original state, if the list is empty
    (fun ys => (ys.map (fun y => y.fst), ((fun y => y.snd) <$> ys.head?).getD s)) <$> taken

instance [Monad m] [MonadState σ m] : MonadState σ (WithManyT m) where
  get := MonadLift.monadLift (MonadState.get : m σ)
  set := MonadLift.monadLift ∘ (MonadState.set : σ → m PUnit)
  modifyGet {α} f := MonadLift.monadLift ((MonadState.modifyGet f) : m α)
