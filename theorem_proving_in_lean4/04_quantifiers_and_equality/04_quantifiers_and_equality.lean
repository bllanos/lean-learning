-- # Examples

-- ## 4.1 The universal quantifier

example (α : Type) (p q : α → Prop) :
  (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
    fun y : α =>
      show p y from (h y).left

example (α : Type) (p q : α → Prop) :
  (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
    show p z from And.left (h z)

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r hab (trans_r (symm_r hcb) hcd)

-- ## 4.2 Equality

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α : Sort u)
#check @Eq.trans.{u} α

variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example : a = d :=
  (hab.trans hcb.symm).trans hcd

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl (f a)
example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl ((fun x => f x) a)

example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

#check Eq.subst

example (α : Type) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

variable (a b c : Nat)
example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) :
  (x + y) * (x + y) =
  x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- ## 4.3 Calculational proofs

variable (a b c d e : Nat)

theorem T
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
calc
  a = b := h1
  _ = c + 1 := h2
  _ = d + 1 := congrArg Nat.succ h3
  _ = 1 + d := Nat.add_comm d 1
  _ = e := Eq.symm h4

theorem T2
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
calc
    a = b := by rw [h1]
  _ = c + 1 := by rw [h2]
  _ = d + 1 := by rw [h3]
  _ = 1 + d := by rw [Nat.add_comm]
  _ = e := by rw [h4]

theorem T3
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e :=
calc
  a = d + 1 := by rw [h1, h2, h3]
  _ = 1 + d := by rw [Nat.add_comm]
  _ = e := by rw [h4]

theorem T4
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e := by
    rw [h1, h2, h3, Nat.add_comm, h4]

theorem T5
  (h1 : a = b)
  (h2 : b = c + 1)
  (h3 : c = d)
  (h4 : e = 1 + d) :
  a = e := by
    simp [h1, h2, h3, Nat.add_comm, h4]

variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d := h3

def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y

theorem divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

theorem divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    divides x y := h₁
    _ = z := h₂
    divides _ (2 * z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    x | y := h₁
    _ = z := h₂
    _ | 2 * z := divides_mul _ _

variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
  _ = (x + y) * x + (x + y) * y :=
    by rw [Nat.mul_add]
  _ = x * x + y * x + (x + y) * y :=
    by rw [Nat.add_mul]
  _ = x * x + y * x + (x * y + y * y) :=
    by rw [Nat.add_mul]
  _ = x * x + y * x + x * y + y * y :=
    by rw [←Nat.add_assoc]

variable (x y : Nat)
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

-- ## 4.4 The existential quantifier

example : ∃ x : Nat, x > 0 :=
  suffices h : 1 > 0 from Exists.intro 1 h
  Nat.zero_lt_succ 0

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

example : ∃ x : Nat, x > 0 :=
  suffices h : 1 > 0 from ⟨1, h⟩
  Nat.zero_lt_succ 0

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩


section
variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
end

#print gex1

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
        show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
  -- Can also uncurry arguments
    (fun w (hw : p w ∧ q w) =>
      show ∃ x, q x ∧ p x from ⟨w, ⟨hw.right, hw.left⟩⟩)

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
  IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

theorem even_plus_even2 (h1 : IsEven a) (h2 : IsEven b) : IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, show a + b = 2 * (w1 + w2) by rw [hw1, hw2, Nat.mul_add]⟩

section
  open Classical
  variable (p : α → Prop)

  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction
      (fun h1 : ¬ ∃ x, p x =>
        have h2 : ∀ x, ¬ p x :=
          fun x =>
          fun h3 : p x =>
          have h4 : ∃ x, p x := ⟨x, h3⟩
          show False from h1 h4
        show False from h h2)
end

section
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ _x : α, r) → r := fun h =>
    match h with
    | ⟨_w, hw⟩ => hw

  example (a : α) : r → (∃ _x : α, r) := fun (h : r) =>
  --  ⟨a, h⟩
    Exists.intro a h

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := Iff.intro
    (fun (h : ∃ x, p x ∧ r) =>
      have h1 : ∃ x, p x := h.elim (fun w hw => ⟨w, hw.left⟩)
      have h2 : r := h.elim (fun _w hw => hw.right)
      And.intro h1 h2)
    (fun (h : (∃ x, p x) ∧ r) =>
      h.left.elim (fun w hw =>
        have hr : r := h.right
        Exists.intro w (And.intro hw hr)))

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := Iff.intro
    (fun (h : ∃ x, p x ∨ q x) =>
      h.elim (fun w hw =>
        Or.elim hw
          (fun hleft => Or.inl (Exists.intro w hleft))
          (fun hright => Or.inr (Exists.intro w hright))))
    (fun (h : (∃ x, p x) ∨ (∃ x, q x)) =>
      Or.elim h
        (fun hleft => hleft.elim (fun w hw => ⟨w, Or.inl hw⟩))
        (fun hright => hright.elim (fun w hw => ⟨w, Or.inr hw⟩)))

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := Iff.intro
    (fun (h : (∀ x, p x)) => fun (hex : (∃ x, ¬ p x)) =>
      hex.elim (fun w hw => absurd (h w) hw))
    (fun (hneg : ¬ (∃ x, ¬ p x)) => fun x =>
      byContradiction (fun (hnp : ¬ p x) =>
        have hex : ∃ x, ¬ p x := ⟨x, hnp⟩
        absurd hex hneg))

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := Iff.intro
    (fun (hex : ∃ x, p x) => fun (hall : ∀ x, ¬ p x) =>
      hex.elim (fun w hw => absurd hw (hall w)))
    (fun (hnotall : ¬ (∀ x, ¬ p x)) =>
      byContradiction (fun (hnex : ¬ (∃ x, p x)) =>
        have fpx : (∀ x, ¬ p x) := fun w => fun hw =>
          show False from hnex (Exists.intro w hw)
        absurd fpx hnotall))

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := Iff.intro
    (fun (hnex : ¬ ∃ x, p x) => fun x => fun hpx =>
      show False from (hnex (Exists.intro x hpx)))
    (fun (hall : ∀ x, ¬ p x) => fun hex =>
      show False from hex.elim (fun w hw => (hall w hw)))

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := Iff.intro
    (fun (hall : ¬ ∀ x, p x) => byContradiction (fun (hnex : ¬ (∃ x, ¬ p x)) =>
      have fall : ∀ x, p x := fun x => byContradiction (fun hnpx : ¬ p x =>
        show False from hnex (Exists.intro x hnpx))
      hall fall))
    (fun (hex : ∃ x, ¬ p x) => fun (hall : ∀ x, p x) =>
      show False from (hex.elim (fun w hw => hw (hall w))))

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := Iff.intro
    (fun (hall : ∀ x, p x → r) =>
      (fun (hexists : ∃ x, p x) =>
        let ⟨x, hx⟩ := hexists
        hall x hx))
    (fun (h : (∃ x, p x) → r) =>
      (fun (x : α) (hx : p x) =>
        h (Exists.intro x hx)))

  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := Iff.intro
    (fun (hexists : ∃ x, p x → r) =>
      (fun (hall : ∀ x, p x) =>
        hexists.elim (fun w hw =>
          hw (hall w))))
    (fun (hall_r : (∀ x, p x) → r) =>
      have f : (∀ x, p x) → (∃ x, p x → r) := (fun (hall : ∀ x, p x) =>
        Exists.intro a (fun _hpa => (hall_r hall)))
      have f_not : ¬(∀ x, p x) → (∃ x, p x → r) := (fun (hneg_all : ¬(∀ x, p x)) =>
        have h₁ : ∃ x, ¬ p x := (not_forall (p := p)).mp hneg_all
        have h₂ : (∃ x, (¬ p x) ∨ r) := Exists.elim h₁ (fun w hw =>
            Exists.intro w (Or.inl hw))
        have h₃ : ∃ x, p x → r := Exists.elim h₂ (fun w hw =>
            Exists.intro w (fun hpx => Or.elim hw
              (fun hnpx => absurd hpx hnpx)
              (fun hr => hr)))
        show ∃ x, p x → r from h₃)

      byCases (p := (∀ x, p x)) f f_not
    )

  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := Iff.intro
    (fun (h : (∃ x, r → p x)) => (fun hr : r =>
      Exists.elim h (fun w hw => Exists.intro w (hw hr))))
    (fun (h : (r → ∃ x, p x)) => byContradiction (fun hnot_exists : ¬(∃ x, r → p x) =>
      have h₁ : ∀ x, ¬(r → p x) := not_exists.mp hnot_exists
      have h₂ : ¬(r → p a) := h₁ a
      have h₃ : r ∧ ¬(p a) := not_imp_iff_and_not.mp h₂
      have h₄ : ∃ x, p x := h h₃.left
      have h₅ : ∃ x, r → p x := h₄.elim (fun w hw =>
        Exists.intro w (fun _hr => hw))
      absurd h₅ hnot_exists))
end

-- ## 4.5 More on the proof language

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  -- show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
  show f 0 ≤ f 3 from Nat.le_trans ‹f 0 ≤ f 2› (h 2)

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

example (n : Nat) : Nat := ‹Nat›
