-- # Examples

def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

-- theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
--   n + Tail.sum xs = Tail.sumHelper n xs := by
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [Tail.sum, Tail.sumHelper]
--     -- stuck

-- theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
--   funext xs
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [Tail.sum, Tail.sumHelper, NonTail.sum]
--     rw [ih]

theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

-- # Practice

theorem non_tail_sum_cons (xs : List Nat) (x : Nat) : NonTail.sum (x :: xs) = x + NonTail.sum xs := by
  simp [NonTail.sum]

-- forall version ends up being the same
theorem non_tail_sum_cons2 (xs : List Nat) : (x : Nat) → NonTail.sum (x :: xs) = x + NonTail.sum xs := by
  simp [NonTail.sum]

-- This is the goal at which the proof of `helper_add_sum_accum` became stuck in the book.
theorem tail_helper_sum_cons (xs : List Nat) :
    (x y : Nat) → Tail.sumHelper (y + x) xs = x + Tail.sumHelper y xs := by
  induction xs with
  | nil =>
    intro x y
    simp [Tail.sumHelper] -- Can probably also use `simp_arith` to satisfy the goal
    rw [Nat.add_comm]
  | cons z zs ih =>
    intro x y
    simp [Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [ih]

theorem tail_sum_cons (xs : List Nat) : (x : Nat) → Tail.sum (x :: xs) = x + Tail.sum xs := by
  induction xs with
  | nil =>
    intro x
    rfl
  | cons y ys _ => -- Unused induction hypothesis means the induction tactic is unnecessary
    intro x
    simp [Tail.sum, Tail.sumHelper]
    exact tail_helper_sum_cons ys x y

-- Same theorem, but not proven by induction
theorem tail_sum_cons2 (xs : List Nat) : (x : Nat) → Tail.sum (x :: xs) = x + Tail.sum xs := by
  intro x
  simp [Tail.sum, Tail.sumHelper]
  rw [←Nat.zero_add (Tail.sumHelper x xs)]
  rw [←tail_helper_sum_cons xs x 0]
  rw [Nat.zero_add]
  rw [Nat.zero_add]

-- Alternative proof that uses lemmas describing the effect on the result
-- of each function of extending the argument by one element.
-- I think this is easier for me to understand than the proof in the book,
-- but the overall proof is longer.
theorem non_tail_sum_eq_tail_sum2 : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [tail_sum_cons2]
    rw [non_tail_sum_cons]
    rw [ih]
