def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
#check woodlandCritters
#check hedgehog
#eval woodlandCritters
#eval hedgehog

-- Compile-time error:
-- def oops := woodlandCritters[3]

-- ## Propositions and Proofs

def onePlusOneIsTwo: 1 + 1 = 2 := rfl
-- def onePlusOneIsFifteen: 1 + 1 = 15 := rfl
#check rfl -- Type a = a
#check Sort
#check onePlusOneIsTwo
#check Type
-- Proposition is a type
#check Prop

-- This is both a proposition and a type definition
def OnePlusOneIsTwo2 : Prop := 1 + 1 = 2
-- This shows that the type is inhabited, because `rfl` is a constructor
theorem onePlusOneIsTwo2 : OnePlusOneIsTwo2 := rfl

-- ## Tactics

theorem onePlusOneIsTwo3 : 1 + 1 = 2 := by
  simp -- The simplification tactic

-- ## Connectives

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := -- by
  -- simp -- Does not work, because it fails to prove `"Str".append "ing" = "String"`?
  And.intro rfl rfl

theorem addOrAppend : 1 + 1 = 2 ∨ "Str".append "ing" = "String" := -- by
  -- simp -- or
  -- Or.inl rfl -- or
  Or.inr rfl

theorem AAndBImpliesAOrB : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem AAndBImpliesAOrB2 {A B : Prop} (andEvidence : A ∧ B) : A ∨ B :=
  match andEvidence with
  | And.intro a _ => Or.inl a

#check AAndBImpliesAOrB2
#check (AAndBImpliesAOrB2)
#check True.intro
#check AAndBImpliesAOrB2 (And.intro True.intro True.intro)
-- "invalid universe level, 0 is not greater than 0"?
-- #eval AAndBImpliesAOrB2 (And.intro True.intro True.intro)

-- Connectives:
-- ------------
-- True.intro : True
-- False : No evidence
-- And.intro : A → B → A ∧ B
-- Or.inl : A → A ∨ B | Or.inr : B → A ∨ B
-- A → B : Function that transforms evidence of A into evidence of B
-- ¬A : Function that transforms evidence of A into evidence of False

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp
theorem falseImpliesTrue2 : False → True :=
  fun _falseEvidence => True.intro

-- ## Evidence as arguments

-- def third (xs : List α) : α := xs[2]
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
-- The truth of the premises imply the truth of the conclusion,
-- which is, in this case, that the third element of `xs` exists.

-- Unsolved goal: 2 < woodlandCritters.length ?
-- #eval third woodlandCritters (by simp)
#eval third woodlandCritters (by simp [woodlandCritters])
#check woodlandCritters.length
#eval woodlandCritters.length
theorem woodlandCrittersHasLength3 : woodlandCritters.length = 3 := rfl

-- ## Indexing without evidence

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters
#eval thirdOption ["only", "two"]
-- Crashing the compiler may crash the editor
#eval woodlandCritters[1]!

-- ## Exercises

theorem twoPlusThree : 2 + 3 = 5 := rfl
theorem fifteenMinusEight : 15 - 8 = 7 := rfl
theorem helloWorld : "Hello".append " world" = "Hello world" := rfl
-- simp made no progress until it is provided with definitions to use in the proof
theorem helloWorld2 : "Hello".append " world" = "Hello world" := (by simp [String.append])
theorem fiveLessThanEighteen : 5 < 18 := by simp
#check (LT.lt)
#check (LT.lt 5)
#check (LT.lt 5 18)

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]
#eval fifth [1, 2, 3, 4, 5] (by simp)
abbrev sequence1 := [1, 2, 3, 4, 5]
#eval fifth sequence1 (by simp)
def sequence2 := [1, 2, 3, 4, 5]
#eval fifth sequence2 (by (simp [sequence2]))
