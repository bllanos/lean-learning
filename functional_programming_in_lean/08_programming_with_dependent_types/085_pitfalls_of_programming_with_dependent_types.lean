-- # Examples

def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => (plusL n k) + 1

-- This version is similar to the standard library's version of addition
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => (plusR n k) + 1

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- """
-- type mismatch
--   cons x (append xs v)
-- has type
--   Vect α (n✝ + k + 1) : Type ?u.1362
-- but is expected to have type
--   Vect α (n✝ + 1 + k) : Type ?u.1362
-- """
-- def Vect.append : Vect α n → Vect α k → Vect α (n + k)
--   | .nil, v => v
--   | .cons x xs, v => .cons x (append xs v)

-- Switching the order of addition of `n` and `k` allows the function
-- to be compiled.
def Vect.append : Vect α n → Vect α k → Vect α (k + n)
  | .nil, v => v
  | .cons x xs, v => .cons x (append xs v)

-- def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
--   | .nil, ys => _ -- Goal: `Vect α (Nat.plusL 0 k)`
--   | .cons x xs, ys => _ -- Goal: `Vect α ((n✝ + 1).plusL k)`

-- ## Definitional equality

-- def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
--   | 0, k, .nil, ys => _ -- Goal: `Vect α (Nat.plusL 0 k)`
--   | n + 1, k, .cons x xs, ys => _ -- Goal: `Vect α ((n + 1).plusL k)`

-- def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
--   -- `Vect α (Nat.plusL 0 k)` is definitionally equal to `Vect α k`
--   | 0, k, .nil, ys => (_ : Vect α k)
--   -- `Vect α ((n + 1).plusL k)` is definitionally equal to `Vect α ((n.plusL k) + 1)`
--   | n + 1, k, .cons x xs, ys => (_ : Vect α ((n.plusL k) + 1))

-- Fill in the placeholders by finding expressions that have the expected types
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (ys : Vect α k)
  | n + 1, k, .cons x xs, ys =>
    (.cons x (
      appendL n k xs ys : Vect α (n.plusL k)) :
      Vect α ((n.plusL k) + 1))

def appendL2 : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL2 xs ys)

-- ## Getting stuck on addition

def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | xs, .nil => xs
  | xs, .cons y ys => .cons y (appendR xs ys)

-- Why?

-- def appendR2 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
--   | 0, k, .nil, ys => (_ : Vect α k)
--   | n + 1, k, .cons x xs, ys => _

-- ## Propositional equality

-- def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
--   | 0 => (_ : 0 = Nat.plusR 0 0)
--   | k + 1 => (_ : k + 1 = Nat.plusR 0 (k + 1))

def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  -- `rfl` is the same as `rfl (a := 0)`.
  -- Why does the book write `by rfl`, when a direct proof without
  -- tactics is simple?
  | 0 => rfl (a := 0) -- Relies on definitional equality
  -- Relies on congruence
  -- Relies on definitional equality between
  -- `Nat.plusR 0 (k + 1)` and `(Nat.plusR 0 k) + 1`
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)

-- def appendR2 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
--   | 0, k, .nil, ys => plusR_zero_left k ▸ (ys : Vect α k)
--   | n + 1, k, .cons x xs, ys => _

def plusR_zero_left2 : (k : Nat) → Nat.plusR 0 k = k
  | 0 => rfl (a := 0)
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left2 k)

-- It seems like `▸` replaces the left-hand argument of the propositional equality
-- statement with the right-hand side, as the following produces
-- a type error. Its documentation says that it tries both orientations
-- of the equality proof, however, but maybe one orientation is tested on
-- the expression and the other is tested on the type expected from the context?
-- def appendR2 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
--   | 0, k, .nil, ys => (plusR_zero_left2 k ▸ ys)
--   | n + 1, k, .cons x xs, ys => _

-- def appendR2 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
--   | 0, k, .nil, ys => plusR_zero_left k ▸ ys
--   | n + 1, k, .cons x xs, ys =>
--       (.cons x ((appendR2 n k xs ys) : Vect α (n.plusR k)) : Vect α (Nat.plusR (n + 1) k))

def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = (Nat.plusR n k) + 1
  | 0 => rfl
  -- Relies on congruence to get
  -- `Nat.plusR (n + 1) k = (Nat.plusR n k) + 1`
  -- Relies on definitional equality between
  -- `Nat.plusR (n + 1) (k + 1)` and `(Nat.plusR (n + 1) k) + 1`
  -- and
  -- `(Nat.plusR n (k + 1)) + 1` and `(Nat.plusR n k) + 1 + 1`
  -- to get `Nat.plusR (n + 1) (k + 1) = (Nat.plusR n (k + 1)) + 1`
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)

def appendR2 : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
      (plusR_succ_left n k) ▸ ((.cons x ((appendR2 n k xs ys))) : Vect α ((n.plusR k) + 1))

def appendR3 : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR3 xs ys)

def appendR4 : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left k ▸ ys
  -- Is it possible to write an explicit expression for the placeholder that
  -- satisfies `(_ + 1 = n)`? I don't think so.
  | (.cons x xs : Vect α _), ys => plusR_succ_left _ k ▸ .cons x (appendR3 xs ys)

-- # Exercises

def plusR_equivalent_to_plus (n k : Nat) : n.plusR k = n + k :=
  match k with
  | 0 => rfl (a := n)
  -- It feels like using `+` as the first argument of `congrArg`
  -- introduces circular reasoning about `+`.
  | k' + 1 => (congrArg (· + 1) (plusR_equivalent_to_plus n k') : n.plusR (k' + 1) = n + (k' + 1))

-- Changing the order of the arguments to `plusR` allows definitional
-- equality to be used alone for type checking.
def appendR5 : Vect α n → Vect α k → Vect α (k.plusR n)
  | .nil, v => v
  | .cons x xs, v => .cons x (appendR5 xs v)

-- Changing the argument used for pattern matching allows definitional
-- equality to be used alone for type checking.
def appendR6 : Vect α n → Vect α k → Vect α (n.plusR k)
  | xs, .nil => xs
  | xs, .cons y ys => .cons y (appendR6 xs ys)
