import NJV_CallerBounds

set_option autoImplicit false
namespace NKB_CallerPrefix
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open OraclePortFrozenOrder

/-- The exact node-count prefix has its exact width. The fit fact is supplied
by the source's capacity check on the SAME slot and count, not assumed at a root. -/
theorem counted (slot : Slice U8) (count : Nat) (fits : 32*count≤slot.val.length) :
 (MultiproofConeSlotTail.prefixNodes slot count).val.length=32*count := by
 simp only [MultiproofConeSlotTail.prefixNodes,List.length_take,Nat.min_eq_left fits]

/-- Instantiate NJV's admitted byte bound at the same scratch and prefix.
The well-formedness producer is separate; no <=10 strengthening is introduced. -/
theorem bytes (slot : Slice U8) (s : reference.Scratch)
    (well : wellFormed (NJV_UnitDomain.keys s))
    (fits : 32*nodeCount 18 (NJV_UnitDomain.keys s)≤slot.val.length) :
 (MultiproofConeSlotTail.prefixNodes slot (nodeCount 18 (NJV_UnitDomain.keys s))).val.length≤9216 := by
 exact NJV_CallerBounds.from_count _ s well (counted slot _ fits)

#print axioms counted
#print axioms bytes
end NKB_CallerPrefix
