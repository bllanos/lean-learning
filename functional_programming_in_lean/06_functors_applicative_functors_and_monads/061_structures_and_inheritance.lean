-- # Examples

structure MythicalCreature where
  large : Bool
deriving Repr

#check MythicalCreature.mk
#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large := true
  vulnerability := "sunlight"

#check Monster.mk

#eval troll.toMythicalCreature

def troll2 : Monster := {large := true, vulnerability := "sunlight"}
def troll3 : Monster := ⟨⟨true⟩, "sunlight"⟩

#eval troll3.large
#eval MythicalCreature.large troll3.toMythicalCreature

def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large

#eval troll3.small
#eval MythicalCreature.small troll3.toMythicalCreature

-- ## Multiple inheritance

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := false
  assistance := "heavy labour"
  payment := "toy goats"
  vulnerability := "sunlight"

#check MonstrousAssistant.mk
#check MonstrousAssistant.toHelper
#check MonstrousAssistant.toMonster
#print MonstrousAssistant.toMonster
#print MonstrousAssistant.toHelper

-- ## Default declarations

inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by simp [huldre]

-- ## Type class inheritance
