import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace AspisR1.CuSavingsS2Tables
def groups : List Nat := [0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7]
def masks : List Nat := [32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024]
def active : List Nat := [6144,6144,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6144,4097,2048,6145,2049,2048,6145,2049,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,6145,4097,6145,6145,4097,26214,26214,26214,26214,26214,26214,1749]
def tau : List Nat := [3,4,2,0,1]

def row (coefficient : Nat) : Nat :=
  (List.range 5).foldl (fun out d =>
    out ||| (((coefficient >>> (2*d)) &&& 3) <<< (2*(tau.getD d 0)))) 0

def inactive (coefficient : Nat) : Bool :=
  !((active.getD (row coefficient / 16) 0).testBit (row coefficient % 16))

def groupValue (j : Fin 64) : Nat := groups.getD j.val 0

theorem groupValue_lt (j : Fin 64) : groupValue j < 12 := by
  fin_cases j <;> decide

def group (j : Fin 64) : Fin 12 := ⟨groupValue j,groupValue_lt j⟩

def groupMask (g : Fin 12) (bit : Fin 16) : Bool :=
  (masks.getD g.val 0).testBit bit.val

theorem lengths : groups.length = 64 ∧ masks.length = 12 ∧ active.length = 64 ∧ tau.length = 5 := by
  decide

#print axioms groupValue_lt
#print axioms lengths
end AspisR1.CuSavingsS2Tables
