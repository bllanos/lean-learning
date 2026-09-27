-- # Examples

-- ## 5.1 Entering tactic mode

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

#print test2

theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case right => exact hp
    case left => exact hq

theorem test5 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

theorem test6 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp

-- ## 5.2 Basic tactics

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    apply Or.elim (And.right h)
    · intro hq
      apply Or.inl
      apply And.intro
      · exact And.left h
      · exact hq
    · intro hr
      apply Or.inr
      apply And.intro
      · exact And.left h
      · exact hr
  · intro h
    apply Or.elim h
    · intro hpq
      apply And.intro
      · exact And.left hpq
      · apply Or.inl
        exact And.right hpq
    · intro hpr
      apply And.intro
      · exact And.left hpr
      · apply Or.inr
        exact And.right hpr

example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

section
  variable (x y z w : Nat)

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
    apply Eq.trans h₁
    apply Eq.trans h₂
    assumption -- h₃

  example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
    apply Eq.trans
    assumption
    apply Eq.trans
    assumption
    assumption
end

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

example: ∀ a b c : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

example (y : Nat) : (fun _x : Nat => 0) y = 0 := by
  rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intros
  apply Eq.symm
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- example : 2 + 3 = 5 := by
--  generalize 3 = x
--  sorry

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

-- ## 5.3 More tactics

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl;
  assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  · apply Or.inr
    assumption

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      · apply Or.inl; constructor <;> assumption
      · apply Or.inr; constructor <;> assumption
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; exact hp; apply Or.inr; exact hr

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p with
  | inl a => apply Sum.inr; assumption
  | inr b => apply Sum.inl; assumption

section
  open Nat

  example (P : Nat → Prop)
      (h₀ : P 0) (h₁ : ∀ n, P (succ n))
      (m : Nat) : P m := by
    cases m with
    | zero => exact h₀
    | succ m' => exact h₁ m'
end

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  · intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  · intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption

-- ## 5.4 Structuring tactic proofs

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
