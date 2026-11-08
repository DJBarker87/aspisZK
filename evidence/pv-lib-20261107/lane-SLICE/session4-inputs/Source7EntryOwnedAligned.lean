import PV_STX2_Source7EntryOwnedIndexed
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryOwnedAligned
open PV_EVHB_OWNER PV_STX2_Source7EntryOwned
/-- Slice-11 adds exactly typed reference alignment to the existing entry
obligation. M31 has element alignment four in the pinned client layout. The
same chosen headers and registrations are retained, without re-selection. -/
structure Source7EntryOwned'''' (s : OWNER) (value : Foundation) : Prop where
  previous : PV_STX2_Source7EntryOwnedIndexed.Source7EntryOwned''' s value
  aligned : ∀ i : Fin value.c1.val.length,
    (PV_STX2_Source7EntrySelection.header previous.owned i).pointer % 4 = 0
/-- The caller's existing Foundation-construction obligation, refined only
by the reference validity clause authorized in LOG D912. -/
def FoundationConstructionEntryObligation'''' (s : OWNER) (value : Foundation) : Prop :=
  Source7EntryOwned'''' s value
/-- Literal implication to the unchanged old obligation. -/
theorem forget {s : OWNER} {value : Foundation} (entry : Source7EntryOwned'''' s value) :
    PV_STX2_Source7EntryOwnedIndexed.FoundationConstructionEntryObligation''' s value :=
  entry.previous
/-- Entry provenance supplies alignment for every column, including every
iteration of the source7 loop, and for zero-length typed regions. -/
theorem column {s : OWNER} {value : Foundation} (entry : Source7EntryOwned'''' s value)
    (i : Fin value.c1.val.length) :
    (PV_STX2_Source7EntrySelection.header entry.previous.owned i).pointer % 4 = 0 :=
  entry.aligned i
/-- Transport of typed entry validity uses the identical source header
preserved by the run, never destination freshness or a pointer alias premise. -/
theorem registered_header {s : OWNER} {value : Foundation}
    (entry : Source7EntryOwned'''' s value) (i : Fin value.c1.val.length)
    (current : OWNER)
    (preserved : PV_EVHB_OWNER.receiver current (PV_STX2_Source7EntrySelection.place entry.previous.owned i) =
      some (PV_STX2_Source7EntrySelection.identity entry.previous.owned i,
        PV_STX2_Source7EntrySelection.header entry.previous.owned i)) :
    ∃ id h, PV_EVHB_OWNER.receiver current (PV_STX2_Source7EntrySelection.place entry.previous.owned i) =
      some (id,h) ∧ h.pointer % 4 = 0 :=
  ⟨_,_,preserved,entry.aligned i⟩
#print axioms Source7EntryOwned''''
#print axioms FoundationConstructionEntryObligation''''
#print axioms forget
#print axioms column
#print axioms registered_header
end PV_STX2_Source7EntryOwnedAligned
