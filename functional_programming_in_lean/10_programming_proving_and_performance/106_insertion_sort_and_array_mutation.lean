-- # Examples

#check dbgTraceIfShared

-- ## The inner loop

def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, hi⟩ =>
    have hi' : i' < arr.size := by
      omega
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', by simp [Array.size_swap, hi, hi']⟩

-- ## The outer loop

partial def insertionSortLoopPartial [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoopPartial (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr

#eval insertionSortLoopPartial #[5, 17, 3, 8] 0
#eval insertionSortLoopPartial #["metamorphic", "igneous", "sedimentary"] 0

-- ### Termination

-- def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
--   if h : i < arr.size then
--     have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
--       sorry
--     insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
--   else
--     arr
-- termination_by arr.size - i

-- theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
--     (insertSorted arr i).size = arr.size := by
--   match i with
--   | ⟨j, isLt⟩ =>
--     induction j generalizing arr with
--     | zero => simp [insertSorted]
--     | succ j' ih =>
--       simp [insertSorted]
--       split <;> try rfl

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt lenEq
    -- Can finish using `simp [insertSorted, *]`
    unfold insertSorted
    exact lenEq
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    -- split <;> try assumption
    -- simp [*]
    split <;> simp [*]

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      omega
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i

-- ## The driver function

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

#eval insertionSort #[3, 1, 7, 4]
#eval insertionSort #["quartz", "marble", "granite", "hematite"]

-- ## Is this really insertion sort?
