-- Quicksort translated from [F*'s tutorial](https://fstar-lang.org/tutorial/)
-- This version sorts lists, not arrays.

def sorted [LT α] [DecidableLT α] (xs: List α) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: xs =>
    if x < y then
      sorted (y :: xs)
    else
      false

def count [DecidableEq α] (y : α) (xs : List α) : Nat :=
  match xs with
  | x :: xs =>
    (if x = y then 1 else 0) + count y xs
  | [] => 0

def mem [DecidableEq α] (y : α) (xs : List α) : Bool :=
  count y xs > 0

def is_permutation [DecidableEq α] (xs ys : List α) :=
  (x : α) → count x xs = count x ys

theorem append_count [DecidableEq α] (xs ys : List α) :
  (x : α) → count x (xs ++ ys) = (count x xs) + (count x ys) := by
  intro x
  induction xs with
  | nil =>
    simp
    rfl
  | cons hd tl ih =>
    simp [count]
    rw [ih]
    rw [Nat.add_assoc]

def partition (f : α → Bool) (xs : List α) :
  { pair : (List α × List α) // pair.fst.length + pair.snd.length = xs.length } :=
  match xs with
  | [] => { val := ⟨[], []⟩, property := by simp }
  | hd :: tl =>
    let { val := ⟨xs, ys⟩, property := h } := partition f tl
    if f hd then
      { val := ⟨hd :: xs, ys⟩, property := (by
        simp
        rw [←h]
        rw [Nat.add_assoc, Nat.add_comm 1 ys.length, ←Nat.add_assoc]
        ) }
    else
      { val := ⟨xs, hd :: ys⟩, property := (by
        simp
        rw [←Nat.add_assoc]
        rw [←h]
        ) }

def sort [LT α] [DecidableLT α] (xs : List α) : List α :=
  match xs with
  | [] => []
  | pivot :: tl =>
    let f := (pivot < ·)
    let { val := ⟨hi, lo⟩, property := h } := partition f tl
    have : lo.length < tl.length + 1 := by
      rw [←h]
      simp
      omega
    have : hi.length < tl.length + 1 := by
      rw [←h]
      simp
      omega
    (sort lo) ++ (pivot :: (sort hi))
termination_by xs.length

-- The proof that `sort` is correct is more difficult to translate from F*...

-- #eval sort [5, 4, 3, 2, 1]
-- #eval sort [1, 2, 3, 4, 5]
-- #eval sort ([] : List Nat)
-- #eval sort [1]
-- #eval sort [1, 5]
-- #eval sort [4, 1, 4, 3]

def getLines : IO (List String) := do
  let stdin ← IO.getStdin
  let mut lines : List String := []
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
    -- Drop trailing newline
    lines := (currLine.dropRight 1) :: lines
    currLine ← stdin.getLine
  pure lines.reverse

def mainUnique : IO Unit := do
  let lines ← getLines
  for line in sort lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "-- Sorted lines: --"
  for line in sort lines do
    IO.println line

  IO.println ""
  IO.println "-- Original data: --"
  for line in lines do
    IO.println line

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--shared"] => mainShared; pure 0
  | ["--unique"] => mainUnique; pure 0
  | _ =>
    IO.println "Expected single argument, either \"--shared\" or \"--unique\""
    pure 1
