theorem nat_neq_neg_one : ∀ (n : Nat), Int.ofNat n ≠ -1 := by
  simp

theorem neg_one_not_in_nat : ¬∃ (n : Nat), Int.ofNat n = -1 := by
  simp
