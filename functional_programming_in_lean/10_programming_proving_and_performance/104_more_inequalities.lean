-- # Examples

-- ## Merge sort

def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
termination_by xs.length + ys.length

def merge2 [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge2 xs' (y' :: ys')
    | .gt => y' :: merge2 (x'::xs') ys'
termination_by (xs, ys)

#check WellFoundedRelation

def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

-- def mergeSort [Ord α] (xs : List α) : List α :=
--   if h : xs.length < 2 then
--     match xs with
--     | [] => []
--     | [x] => [x]
--   else
--     let halves := splitList xs
--     merge (mergeSort halves.fst) (mergeSort halves.snd)
-- termination_by xs.length

-- ## Splitting a list makes it shorter

theorem Nat.le_succ_of_le2 : n ≤ m → n ≤ m + 1
  | h => Nat.le.step h

theorem Nat.le_succ_of_le3 : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => constructor; assumption

theorem Nat.le_succ_of_le4 : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih

theorem Nat.le_succ_of_le5 (h : n ≤ m) : n ≤ m + 1 := by
  induction h <;> repeat (first | constructor | assumption)

theorem Nat.le_succ_of_le6 : n ≤ m → n ≤ m + 1 := by
  apply Nat.le.step

theorem Nat.le_succ_of_le7 (h : n ≤ m) : n ≤ m + 1 := by
  omega

theorem Nat.le_succ_of_le8 : n ≤ m → n ≤ m + 1
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le8 h)

theorem splitList_shorter_le (lst : List α) :
  (splitList lst).fst.length ≤ lst.length ∧
    (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih with
    | intro ih_left ih_right =>
      constructor
      case left => exact ih_right
      case right => apply Nat.le_succ_of_le ih_left

theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
  (splitList lst).fst.length < lst.length ∧
    (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
    apply splitList_shorter_le

theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right

structure And2 (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

-- ## Merge sort terminates

-- `sorry` can be used for code or for proofs
-- def f (a : Nat) : Nat := by sorry

-- def mergeSort [Ord α] (xs : List α) : List α :=
--   if h : xs.length < 2 then
--     match xs with
--     | [] => []
--     | [x] => [x]
--   else
--     let halves := splitList xs
--     have : halves.fst.length < xs.length := by
--       sorry
--     have : halves.snd.length < xs.length := by
--       sorry
--     merge (mergeSort halves.fst) (mergeSort halves.snd)
-- termination_by xs.length

def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by
      omega
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length

#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
#eval mergeSort [5, 3, 22, 15]

-- ## Division as iterated subtraction

-- def div (n k : Nat) : Nat :=
--   if n < k then
--    0
--   else
--     1 + div (n - k) k

def div (n k : Nat) (ok : k ≠ 0): Nat :=
  if h : n < k then
   0
  else
    1 + div (n - k) k ok
termination_by n -- Optional

-- # Exercises

theorem zero_lt_succ_n : (n : Nat) → 0 < n + 1
  | .zero => Nat.lt.base 0
  | .succ m =>
    let ih := zero_lt_succ_n m
    Nat.lt.step ih

theorem zero_lt_succ_n2 (n : Nat) : 0 < n + 1 := by omega

-- Mirror of the direct proof above, using tactics
theorem zero_lt_succ_n3 : (n : Nat) → 0 < n + 1 := by
  intro n
  induction n with
  | zero => constructor
  | succ m ih => constructor; assumption

theorem zero_leq_n : (n : Nat) → 0 ≤ n := by
  omega

theorem zero_leq_n2 : (n : Nat) → 0 ≤ n
  | .zero => Nat.le.refl
  | .succ m =>
    let ih := zero_leq_n2 m
    Nat.le.step ih

theorem diff_add_one (n k : Nat) : (n + 1) - (k + 1) = n - k := by
  omega

theorem diff_add_one2 (n k : Nat) : (n + 1) - (k + 1) = n - k :=
  Nat.add_sub_add_right n 1 k

theorem lt_implies_ne_zero (n k : Nat) (h : k < n) : n ≠ 0 := by
  rw [Nat.ne_zero_iff_zero_lt]
  induction k with
  | zero => assumption
  | succ k' ih =>
    let h' : k' < n := Nat.lt_of_succ_lt h
    exact ih h'

theorem lt_implies_ne_zero2 (n k : Nat) (h : k < n) : n ≠ 0 :=
  match k with
  | 0 => Nat.ne_zero_iff_zero_lt.mpr h
  | k' + 1 =>
    let h' : k' < n := Nat.lt_of_succ_lt h
    lt_implies_ne_zero2 n k' h'

theorem sub_self_eq_zero : (n : Nat) → n - n = 0
  | .zero => rfl
  | .succ n' =>
    let ih := sub_self_eq_zero n'
    Nat.succ_sub_succ_eq_sub n' n' ▸ ih

theorem sub_self_eq_zero2 (n : Nat) : n - n = 0 := by simp

theorem succ_lt_implies_lt (n k : Nat) (h : n + 1 < k) : n < k := by
  omega

theorem succ_lt_implies_lt2 (n k : Nat) (h : n + 1 < k) : n < k :=
  Nat.lt_of_add_right_lt h
