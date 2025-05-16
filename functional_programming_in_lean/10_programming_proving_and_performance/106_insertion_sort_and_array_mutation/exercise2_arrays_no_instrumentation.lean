-- Quicksort on arrays
--
-- Lomuto partition scheme variant
--
-- Reference: <https://en.wikipedia.org/wiki/Quicksort#Lomuto_partition_scheme>
--
-- I tried the Hoare partition scheme, but it seems much harder to finish the
-- proof of termination when using that partition scheme. The Hoare partition
-- scheme does not rely on explicit checks against the bounds of the array.

def partitionLoop
    [LT α] [DecidableLT α]
    (arr : Array α)
    (pivot : α)
    (high : Fin arr.size)
    (j : { n : Nat // n ≤ high.val })
    (i : { n : Nat // n ≤ j.val })
  :
    { arrOut : Array α // arrOut.size = arr.size } × { n : Nat // n ≤ high.val ∧ n ≥ i.val }
  :=
  if h : j.val < high.val then
    let newJ := j.val + 1
    if pivot < arr[j.val] then
      partitionLoop arr pivot high ⟨newJ, by omega⟩ ⟨i.val, by simp [newJ]; omega⟩
    else
      let newArray := arr.swap i j
      let newI := i.val + 1
      have h_eq : newArray.size = arr.size := by simp [Array.size_swap, newArray]
      let newHigh : Fin newArray.size := ⟨high.val, by rw [h_eq]; exact high.isLt⟩
      let partitionLoopResult := partitionLoop
          newArray
          pivot
          newHigh
          ⟨newJ, by simp [newJ, newHigh]; omega⟩
          ⟨newI, by simp [newJ]; omega⟩
      ⟨h_eq ▸ partitionLoopResult.fst, ⟨partitionLoopResult.snd, (by
        have hleft := partitionLoopResult.snd.property.left
        simp [newHigh] at hleft
        simp [hleft]
        have hright := partitionLoopResult.snd.property.right
        simp [newI] at hright
        have hright_weak := Nat.le_of_add_right_le hright
        exact hright_weak
        )⟩⟩
  else
    ⟨⟨arr, rfl⟩, ⟨i.val, by omega⟩⟩
termination_by high - j.val

def partition
    [LT α] [DecidableLT α]
    (arr : Array α)
    (high : Fin arr.size)
    (low : { n : Nat // n < high })
  :
    { arrOut : Array α // arrOut.size = arr.size } × { n : Nat // n ≤ high ∧ n ≥ low }
  :=
  let pivot := arr[high]
  let iAndJ := low.val
  let (partitionedArr, i) := partitionLoop arr pivot high ⟨iAndJ, by omega⟩ ⟨iAndJ, by simp⟩
  ⟨⟨partitionedArr.val.swap i high, by simp [Array.size_swap]; rw [partitionedArr.property]⟩, i⟩

def sortHelper
    [LT α] [DecidableLT α]
    (arr : Array α)
    (high : Fin arr.size)
    (low : { n : Nat // n < high })
  :
    { arrOut : Array α // arrOut.size = arr.size }
  :=
  let (partitionedArr, p) := partition arr high low

  let pSubOne := p.val - 1
  let sortedLeft : { arrOut : Array α // arrOut.size = arr.size } := if h : low < pSubOne then
      have : p - 1 - low.val < high - low.val := by
        have p_leq_high : p.val ≤ high := by omega
        omega
      let sortResult := sortHelper partitionedArr.val ⟨pSubOne, by omega⟩ ⟨low.val, by simp; omega⟩
      ⟨sortResult.val, by rw [sortResult.property, partitionedArr.property]⟩
    else
      partitionedArr

  let pAddOne := p.val + 1
  let sortedRight : { arrOut : Array α // arrOut.size = arr.size } := if h : pAddOne < high then
      have : high - (p.val + 1) < high - low.val := by
        have p_geq_high : p.val ≥ low := by omega
        omega
      let sortResult := sortHelper sortedLeft ⟨high.val, by omega⟩ ⟨pAddOne, by simp [pAddOne]; omega⟩
      ⟨sortResult.val, by rw [sortResult.property, sortedLeft.property]⟩
    else
      sortedLeft

  sortedRight
termination_by high.val - low.val

def sort
    [LT α] [DecidableLT α]
    (arr : Array α)
  :
    Array α
  := if h : arr.size ≤ 1 then
      arr
    else
      let high : Fin arr.size := ⟨arr.size - 1, by omega⟩
      sortHelper arr high ⟨0, by simp [high]; omega⟩

-- Testing
#eval sort #[5, 4, 3, 2, 1]
#eval sort #[1, 2, 3, 4, 5]
#eval sort (#[] : Array Nat)
#eval sort #[1]
#eval sort #[1, 5]
#eval sort #[5, 5]
#eval sort #[5, 1]
#eval sort #[4, 1, 4, 3]
#eval sort #[10, 8, 6, 4, 2, 0, 1, 3, 5, 7, 9, 10]
#eval sort #[10, 8, 6, 4, 2, 0, 1, 3, 5, 7, 9, 4]
#eval sort #[10, 8, 6, 4, 2, 0, 1, 3, 5, 7, 9, 0]
