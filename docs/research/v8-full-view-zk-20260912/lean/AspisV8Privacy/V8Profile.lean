import Mathlib.Tactic.NormNum

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. Literal numeric contract for the pinned
positive-transfer profile. Norm_num checks arithmetic, NOT source provenance.
The Python audit separately checks the descriptor and inventory fingerprints.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace AspisV8Privacy.V8Profile

def rows : Nat := 1024
def activeRows : Nat := 214
def inactiveRows : Nat := rows - activeRows
def oldSemanticDraws : Nat := 3803
def effectiveSemanticCells : Nat := 3802
def independentSemanticMasks : Nat := effectiveSemanticCells - 16

def totalIdealBaseDimension : Nat :=
  independentSemanticMasks + 10*(rows-1) + 4*((rows-1)+(inactiveRows-1)+(rows-1))

def requestedBaseDraws : Nat :=
  oldSemanticDraws + 10*rows + 4*rows + 4*(inactiveRows-1) + 4*rows

def fixedFields : Nat := 697
def fixedHeader : Nat := fixedFields*16 + 2*26 + 24
def queryRecord : Nat := 403 + 186 + 32
def maxBody : Nat := fixedHeader + 22*queryRecord + 2*296*26

theorem inventory_arithmetic :
    inactiveRows = 810 ∧ independentSemanticMasks = 3786 ∧
    totalIdealBaseDimension = 25436 ∧ requestedBaseDraws = 25471 := by
  norm_num [inactiveRows, rows, activeRows, independentSemanticMasks,
    effectiveSemanticCells, totalIdealBaseDimension, requestedBaseDraws, oldSemanticDraws]

theorem wire_arithmetic : fixedHeader = 11228 ∧ queryRecord = 621 ∧ maxBody = 40282 := by
  decide

/-- The fixed fields are a complete partition. Their secrecy is NOT asserted. -/
theorem field_partition : 1 + 270 + 87 + 1 + 58 + 24 + 256 = fixedFields := by
  norm_num [fixedFields]

#print axioms inventory_arithmetic
#print axioms wire_arithmetic
#print axioms field_partition
end AspisV8Privacy.V8Profile
