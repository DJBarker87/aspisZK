import PV_STX2_Source7EntrySelection
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryHeaderFacts
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_Source7EntryOwned PV_STX2_Source7EntrySelection
/-- Conditional on owner acceptance of the translator patch. TypedMemory's
Valid receiver and the entry-selected receiver are the same header. -/
theorem length {s : OWNER} {foundation : Foundation} (entry : Source7EntryOwned s foundation)
    (i : Fin foundation.c1.val.length) :
    (header entry i).len = (values foundation i).length := by
  obtain ⟨id,h,read,owned,len,capacity⟩ := (selected entry i).2.2.2.2.1
  rw [PV_STX2_Source7EntrySelection.receiver entry i] at read
  cases read
  exact len
/-- Conditional on owner acceptance of the translator patch. Entry ownership
at precisely the selected header; no fresh allocation is inferred. -/
theorem owned {s : OWNER} {foundation : Foundation} (entry : Source7EntryOwned s foundation)
    (i : Fin foundation.c1.val.length) : Owned s.world (header entry i) := by
  obtain ⟨id,h,read,owned,len,capacity⟩ := (selected entry i).2.2.2.2.1
  rw [PV_STX2_Source7EntrySelection.receiver entry i] at read
  cases read
  exact owned
/-- Conditional on owner acceptance of the translator patch. Bytes at the
selected header decode to the original column, at every in-bounds index. -/
theorem decoded {s : OWNER} {foundation : Foundation} (entry : Source7EntryOwned s foundation)
    (i : Fin foundation.c1.val.length) (j : Nat) (bound : j < (values foundation i).length) :
    PV_OWN2_Codec.decodeM31 (PV_STX_OriginalCopyTyped.bytesAt s.world.memory
      (header entry i).pointer 4 j) = some (values foundation i)[j] := by
  exact ((selected entry i).2.2.2.2.2 _ _
    (PV_STX2_Source7EntrySelection.receiver entry i)).2 j bound
#print axioms length
#print axioms owned
#print axioms decoded
end PV_STX2_Source7EntryHeaderFacts
