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

-- ## Alternative proofs for the examples

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

-- ## Proving equivalence of Nat addition functions

-- I think the `funext` tactic is equivalent to a forall proposition
-- Can I substitute `funext` with a forall proposition?
-- No, it's equivalent to adding the arguments to the functions as parameters
-- instead of assumptions. (Parameters must be equivalent to assumptions.)
-- See below.

def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => (plusL n k) + 1

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => (plusR n k) + 1

theorem plusl_plus_1 (n k : Nat) : n.plusL (k + 1) = n.plusL k + 1 := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    unfold Nat.plusL
    rewrite [ih]
    rfl

theorem plusr_plus_1 (n k : Nat) : (n + 1).plusR k = n.plusR k + 1 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    unfold Nat.plusR
    rewrite [ih]
    rfl

theorem plusl_eq_plusr_funext : Nat.plusL = Nat.plusR := by
  funext n k
  induction n with
  | zero => induction k with
    | zero => rfl
    | succ k' ihk =>
      unfold Nat.plusL Nat.plusR
      rewrite [←ihk]
      unfold Nat.plusL
      rfl
  | succ n' ihn =>
    unfold Nat.plusL
    rewrite [ihn]
    rewrite [plusr_plus_1 n' k]
    rfl

theorem plusl_eq_plusr_forall (n k : Nat) : Nat.plusL n k = Nat.plusR n k := by
  induction n with
  | zero => induction k with
    | zero => rfl
    | succ k' ihk =>
      unfold Nat.plusL Nat.plusR
      rewrite [←ihk]
      unfold Nat.plusL
      rfl
  | succ n' ihn =>
    unfold Nat.plusL
    rewrite [ihn]
    rewrite [plusr_plus_1 n' k]
    rfl

-- # Exercises

-- ## Natural number addition

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- It would be better to unfold the definition of +, to avoid relying on a theorem to be proven,
    -- but I'm not sure how to do so without expressing this theorem in terms of a redefinition of +.
    rw [←Nat.add_assoc]
    rw [ih]

theorem zero_add2 (n : Nat) : Nat.plusR 0 n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    unfold Nat.plusR
    rw [ih]

theorem add_assoc (n m k : Nat) : Nat.plusR (Nat.plusR n m) k = Nat.plusR n (Nat.plusR m k) := by
  induction n with
  | zero =>
    rw [zero_add2]
    rw [zero_add2]
  | succ n' ihn =>
    rewrite [plusr_plus_1 n' m]
    rewrite [plusr_plus_1 (n'.plusR m) k]
    rewrite [plusr_plus_1 n' (m.plusR k)]
    rw [←ihn]

theorem add_comm (n m : Nat) : Nat.plusR n m = Nat.plusR m n := by
  induction n with
  | zero =>
    rw [zero_add2]
    rfl
  | succ n' ihn =>
    rewrite [plusr_plus_1]
    rw [ihn]
    rfl

-- ## More accumulator proofs

-- ### Reversing lists

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

theorem non_tail_reverse_eq_helper_accum (xs : List α) :
    (soFar : List α) → (NonTail.reverse xs) ++ soFar = Tail.reverseHelper soFar xs := by
  induction xs with
  | nil =>
    intro soFar
    rfl
  | cons y ys ih =>
    intro soFar
    simp [NonTail.reverse, Tail.reverseHelper]
    exact ih (y :: soFar)

theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
  funext α xs
  unfold Tail.reverse
  rw [←List.append_nil (NonTail.reverse xs)]
  exact non_tail_reverse_eq_helper_accum xs []

-- ### Factorial

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => NonTail.factorial n * (n + 1)

def Tail.factorialHelper (soFar : Nat) : Nat → Nat
  | 0 => soFar
  | n + 1 => factorialHelper (soFar * (n + 1)) n

def Tail.factorial (x : Nat) : Nat :=
  factorialHelper 1 x

theorem non_tail_factorial_eq_helper_accum (x : Nat) :
    (soFar : Nat) → (NonTail.factorial x) * soFar = Tail.factorialHelper soFar x := by
  induction x with
  | zero =>
    intro soFar
    -- simp +arith [NonTail.factorial, Tail.factorialHelper] -- This works too
    unfold NonTail.factorial Tail.factorialHelper
    rw [Nat.mul_comm]
    rw [Nat.mul_one]
  | succ y ih =>
    intro soFar
    simp [NonTail.factorial, Tail.factorialHelper]
    rw [Nat.mul_assoc (NonTail.factorial y) (y + 1) soFar]
    rw [Nat.mul_comm (y + 1) soFar]
    exact ih (soFar * (y + 1))

theorem non_tail_factorial_eq_tail_factorial : NonTail.factorial = Tail.factorial := by
  funext x
  unfold Tail.factorial
  rw [←Nat.mul_one (NonTail.factorial x)]
  exact non_tail_factorial_eq_helper_accum x 1
