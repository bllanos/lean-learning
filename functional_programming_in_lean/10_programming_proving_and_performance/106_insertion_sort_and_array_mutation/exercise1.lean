def reverseHelper (arr : Array α) (i : Fin arr.size) (j : { n : Nat // n < i }) : Array α :=
  have : (dbgTraceIfShared "arr swap" arr).size = arr.size := by
    simp [dbgTraceIfShared]
  let result := (dbgTraceIfShared "arr swap" arr).swap i.val j.val
  let i' := i.val - 1
  let j' := j.val + 1
  if h: j' ≥ i' then
    (dbgTraceIfShared "result base case" result)
  else
    -- A more explicit proof:
    -- reverseHelper result ⟨i', by simp [result, *]; omega⟩ ⟨j', by
    --   simp
    --   rw [Nat.not_ge_eq] at h
    --   let h' := Nat.lt_add_one_of_le h
    --   simp at h'
    --   exact h'
    -- ⟩
    have : (dbgTraceIfShared "result recursive case" result).size = result.size := by
      simp [dbgTraceIfShared]
    reverseHelper (dbgTraceIfShared "result recursive case" result) ⟨i', by simp [result, *]; omega⟩ ⟨j', by simp; omega⟩

def Array.reverse2 (arr : Array α) : Array α :=
  match h: arr.size with
  | 0 => arr
  | 1 => arr
  | n + 2 =>
    reverseHelper arr ⟨n + 1, by omega⟩ ⟨0, by simp⟩

-- #eval (#[] : Array Nat).reverse2
-- #eval #[1].reverse2
-- #eval #[1, 2].reverse2
-- #eval #[1, 2, 3].reverse2
-- #eval #[1, 2, 3, 4].reverse2
-- #eval #[1, 2, 3, 4, 5].reverse2

def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
    -- Drop trailing newline
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  pure lines

def mainUnique : IO Unit := do
  let lines ← getLines
  for line in lines.reverse2 do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "-- Sorted lines: --"
  for line in lines.reverse2 do
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
