-- # Examples

-- ## 3.1 Propositions and types

#check And
#check Or
#check Not
#check _ → _
def Implies (p q : Prop) : Prop := p → q
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q ) r
#check (And p q) → (And q p)
#check Implies (And p q) (And q p)

structure Proof (p : Prop) : Type where
  proof : p
#check Proof
axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_commut p q

axiom modus_ponens (p q : Prop) :
  -- Is this `Implies (And (Implies p q) p) q`?
  Proof (Implies p q) → Proof p → Proof q
#check modus_ponens

axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

-- ## 3.2 Working with propositions as types

set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
#print t1

theorem t1_2 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

theorem t1_3 (hp : p) (hq : q) : p := hp
#print t1_3

axiom hp : p
theorem t2 : q → p := t1 hp
#print t2

axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 := False.elim unsound

theorem t1_4 {p q : Prop} (hp : p) (hq : q) : p := hp
#print t1_4

theorem t1_5 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

variable {p q : Prop}
theorem t1_6 : p → q → p := fun (hp : p) (hq : q) => hp

theorem t1_7 (p q : Prop) (hp : p) (hq : q) : p := hp
variable (p q r s : Prop)

#check t1_7 p q
#check t1_7 r s
#check t1_7 (r → s) (s → r)

variable (h : r → s)

#check t1_7 (r → s) (s → r) h

variable (p q r s : Prop)
theorem t2_2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

-- ## 3.3 Propositional logic

-- The listing below is in order of precedence for the operators

-- True
-- False
-- Not ¬
-- /\ ∧ (right-associative)
-- \/ ∨ (right-associative)
-- -> → (right-associative)
-- <-> ↔ (\lr) (right-associative)

variable (p q : Prop)
#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

-- ### 3.3.1 Conjunction

variable (p q : Prop)
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)
#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩
example (h : p ∨ q) : q ∨ p := Or.elim h
  (λ left => Or.inr left)
  (λ right => Or.inl right)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

-- ### 3.3.2 Disjunction

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

variable (p q r : Prop)
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

example (h: p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

-- ### 3.3.3 Negation and falsity

variable (p q r : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

-- ### 3.3.4 Logical equivalence

variable (p q : Prop)
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))
#check and_swap p q

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

theorem and_swap_2 : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

-- ## 3.4 Introducing auxiliary subgoals

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

example (h : p ∧ q) : q ∧ p :=
  suffices hp : p from
    suffices hq : q from And.intro hq hp
    show q from h.right
  show p from h.left

-- ## 3.5 Classical logic

open Classical

variable (p : Prop)

#check em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

theorem dne_converse_via_em {p : Prop} (h : p) : ¬¬p :=
  Or.elim (em (¬p))
    (fun hnp : ¬p => absurd h hnp)
    (fun hnnp : ¬¬p => hnnp)

theorem dne_converse {p : Prop} (h : p) : ¬¬p :=
  fun hnp => absurd h hnp

theorem not_not_em' (p : Prop) : ¬¬(p ∨ ¬p) :=
  fun hnemp : ¬(p ∨ ¬p) =>
    have h : ¬p ∧ ¬¬p := not_or.mp hnemp
    absurd h.left h.right

theorem em_via_dne (p : Prop) : p ∨ ¬p :=
  (dne (not_not_em' p))

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
      show False from h h1)

variable (p q : Prop)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
            h ⟨hp, hq⟩))
    (fun hp : ¬p => Or.inl hp)

-- ## 3.6 Examples of propositional validities

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
    show q from
      Or.elim (em q)
        (fun hq : q => hq)
        (fun hnq : ¬q => absurd (And.intro hp hnq) h)

-- # Exercises

-- 1. Prove the following identities

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from And.intro h.right h.left)
    (fun h : q ∧ p =>
      show p ∧ q from And.intro h.right h.left)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
        (fun hp : p => show q ∨ p from Or.inr hp)
        (fun hq : q => show q ∨ p from Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h
        (fun hq : q => show p ∨ q from Or.inr hq)
        (fun hp : p => show p ∨ q from Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      And.intro (h.left.left) (And.intro (h.left.right) (h.right)))
    (fun h : p ∧ (q ∧ r) =>
      And.intro (And.intro (h.left) (h.right.left)) h.right.right)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (fun hpq : p ∨ q => Or.elim hpq
          (fun hp : p => Or.inl hp)
          (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r => Or.elim hqr
          (fun hq : q => Or.inl (Or.inr hq))
          (fun hr : r => Or.inr hr))
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hpqr : p ∧ (q ∨ r) =>
      have hp : p := hpqr.left
      Or.elim hpqr.right
        (fun hq : q => Or.inl (And.intro hp hq))
        (fun hr : r => Or.inr (And.intro hp hr)))
    (fun hor : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hor
        (fun hpq : p ∧ q => And.intro hpq.left (Or.inl hpq.right))
        (fun hpr : p ∧ r => And.intro hpr.left (Or.inr hpr.right)))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr : p ∨ (q ∧ r) =>
      Or.elim hpqr
        (fun hp : p => And.intro (Or.inl hp) (Or.inl hp))
        (fun hqr : q ∧ r => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (fun hand : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := hand.left
      have hpr : p ∨ r := hand.right
      Or.elim hpq
        (fun hp : p => Or.inl hp)
        (fun hq : q => Or.elim hpr
          (fun hp : p => Or.inl hp)
          (fun hr : r => Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun himp : p → (q → r) =>
      fun hpq : p ∧ q =>
        himp (hpq.left) hpq.right)
    (fun himp : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          show r from himp (And.intro hp hq))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun himp : p ∨ q → r =>
      And.intro
        (fun hp : p => himp (Or.inl hp))
        (fun hq : q => himp (Or.inr hq)))
    (fun hand : (p → r) ∧ (q → r) =>
      have hpr : p → r := hand.left
      have hqr : q → r := hand.right
      fun hpq : p ∨ q =>
        Or.elim hpq
        (fun hp : p => hpr hp)
        (fun hq : q => hqr hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := Iff.intro
  (fun hnpq : ¬(p ∨ q) =>
    And.intro (fun hp : p => hnpq (Or.inl hp)) (fun hq : q => hnpq (Or.inr hq)))
  (fun hand : ¬p ∧ ¬q =>
    have hnp : p → False := hand.left
    have hnq : q → False := hand.right
    fun hor : p ∨ q =>
      Or.elim hor
        (fun hp : p => hnp hp)
        (fun hq : q => hnq hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) := fun hor : ¬p ∨ ¬q =>
    Or.elim hor
      (fun hnp : ¬p => fun hpq : p ∧ q => hnp hpq.left)
      (fun hnq : ¬q => fun hpq : p ∧ q => hnq hpq.right)
