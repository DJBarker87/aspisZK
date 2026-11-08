import PV_STX2_Source7EntryOwnedAligned
set_option autoImplicit false
/-! All statements are conditional on owner acceptance of the translator patch. -/
noncomputable section
namespace PV_STX2_Source7EntryReferenceValid
open PV_EVHB_OWNER PV_STX2_Source7EntryOwned
/-- LOG D918: the same entry-selected typed slice is non-null, aligned and
its initialized byte range does not wrap the pinned 64-bit address space.
The bound concerns the slice length, not unused RawVec capacity. -/
structure Source7EntryOwned''''' (s : OWNER) (value : Foundation) : Prop where
  previous : PV_STX2_Source7EntryOwnedAligned.Source7EntryOwned'''' s value
  nonnull : ∀ i : Fin value.c1.val.length,
    (PV_STX2_Source7EntrySelection.header previous.previous.owned i).pointer ≠ 0
  bounded : ∀ i : Fin value.c1.val.length,
    (PV_STX2_Source7EntrySelection.header previous.previous.owned i).pointer +
      (values value i).length * 4 ≤ 2^64

def FoundationConstructionEntryObligation''''' (s : OWNER) (value : Foundation) : Prop :=
  Source7EntryOwned''''' s value

theorem forget79 {s : OWNER} {value : Foundation} (entry : Source7EntryOwned''''' s value) :
    PV_STX2_Source7EntryOwnedAligned.FoundationConstructionEntryObligation'''' s value :=
  entry.previous
theorem forget {s : OWNER} {value : Foundation} (entry : Source7EntryOwned''''' s value) :
    PV_STX2_Source7EntryOwnedIndexed.FoundationConstructionEntryObligation''' s value :=
  entry.previous.previous
theorem column {s : OWNER} {value : Foundation} (entry : Source7EntryOwned''''' s value)
    (i : Fin value.c1.val.length) :
    let h := PV_STX2_Source7EntrySelection.header entry.previous.previous.owned i
    h.pointer ≠ 0 ∧ h.pointer % 4 = 0 ∧ h.pointer + (values value i).length*4 ≤ 2^64 :=
  ⟨entry.nonnull i,entry.previous.aligned i,entry.bounded i⟩
#print axioms Source7EntryOwned'''''
#print axioms FoundationConstructionEntryObligation'''''
#print axioms forget79
#print axioms forget
#print axioms column
end PV_STX2_Source7EntryReferenceValid
