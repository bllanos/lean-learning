-- # Examples

-- ## Recursion and induction

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => (plusR n k) + 1

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rewrite [←ih]
    rfl

-- ## Tactic golf

theorem plusR_zero_left2 (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    -- exact ih
    assumption

theorem plusR_zero_left3 (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption

theorem plusR_zero_left4 (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption

-- ## Induction on other datatypes

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
    simp_arith

theorem BinTree.mirror_count2 (t : BinTree α) : t.mirror.count = t.count := by
  induction t with
  | leaf => rfl
  | branch l x r ihl ihr =>
    simp_arith [BinTree.mirror, BinTree.count, ihl, ihr]

theorem BinTree.mirror_count3 (t : BinTree α) : t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp_arith [BinTree.mirror, BinTree.count, *]

theorem BinTree.mirror_count4 (t : BinTree α) : t.mirror.count = t.count := by
  induction t <;> simp_arith [BinTree.mirror, BinTree.count, *]

-- # Exercises

-- ## Exercise 1

theorem plusR_succ_left (n k : Nat) : Nat.plusR (n + 1) k = (Nat.plusR n k) + 1 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    unfold Nat.plusR
    rewrite [←ih]
    rfl

theorem plusR_succ_left2 (n k : Nat) : Nat.plusR (n + 1) k = (Nat.plusR n k) + 1 := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp [Nat.plusR, ih]

-- ## Exercise 2

theorem plusR_succ_left3 (n k : Nat) : Nat.plusR (n + 1) k = (Nat.plusR n k) + 1 := by
  induction k <;> simp [Nat.plusR] <;> assumption

theorem plusR_succ_left4 (n k : Nat) : Nat.plusR (n + 1) k = (Nat.plusR n k) + 1 := by
  induction k <;> simp [Nat.plusR, *]

-- ## Exercise 3

theorem List.append_assoc2 (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  induction xs with
  | nil => induction ys with
    | nil => induction zs with
      | nil => rfl
      | cons z zs ihz => simp [List.append]
    | cons y ys ihy => induction zs with
      | nil => simp [List.append]
      | cons z zs ihz => simp [List.append]
  | cons => induction ys with
    | nil => induction zs with
      | nil => simp [List.append]
      | cons z zs ihz => simp [List.append]
    | cons y ys ihy => induction zs with
      | nil => simp [List.append]
      | cons z zs ihz => simp [List.append]

theorem List.append_assoc3 (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  induction xs <;> induction ys <;> induction zs <;> simp [List.append]
