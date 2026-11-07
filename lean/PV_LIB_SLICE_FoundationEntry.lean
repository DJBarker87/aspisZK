import PV_STX2_Source7EntryReferenceValid
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_FoundationEntry
open PV_EVHB_OWNER PV_STX2_Source7EntryOwned
open PV_STX2_Source7EntryOwnedWellFormed

/-- Exact remaining Foundation-construction caller clauses, on the SAME
entry-selected headers as Source7EntryOwned''. Registration is indexed over
all columns (D812); validity includes empty slices (slice-11', D918).
These are construction obligations, never hypotheses inserted at a copy call. -/
structure CallerClauses {s : OWNER} {value : Foundation}
    (entry : Source7EntryOwned'' s value) : Prop where
  registered : ∀ i : Fin value.c1.val.length,
    s.places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(PV_STX2_Source7EntrySelection.header entry.registered.owned i).pointer,[]⟩) =
    s.places (PV_STX2_Source7EntrySelection.place entry.registered.owned i)
  nonnull : ∀ i : Fin value.c1.val.length,
    (PV_STX2_Source7EntrySelection.header entry.registered.owned i).pointer ≠ 0
  aligned : ∀ i : Fin value.c1.val.length,
    (PV_STX2_Source7EntrySelection.header entry.registered.owned i).pointer % 4 = 0
  bounded : ∀ i : Fin value.c1.val.length,
    (PV_STX2_Source7EntrySelection.header entry.registered.owned i).pointer +
      (values value i).length * 4 ≤ 2^64

/-- Discharge to the EXACT provider-named caller obligation. This is a
conditional assembly theorem, not a proof that the actual Foundation builder
satisfies CallerClauses, nor a claim that ownership entails reference validity.
The provider's translator-patch acceptance qualification is retained. -/
theorem discharge {s : OWNER} {value : Foundation}
    (entry : Source7EntryOwned'' s value) (clauses : CallerClauses entry) :
    PV_STX2_Source7EntryReferenceValid.FoundationConstructionEntryObligation''''' s value :=
  ⟨⟨⟨entry.registered.owned,entry.wellFormed,clauses.registered⟩,
    clauses.aligned⟩,clauses.nonnull,clauses.bounded⟩

/-- Before/after compatibility: every refined caller obligation implies
Source7EntryOwned'', including its existing first-column registration. -/
theorem forget {s : OWNER} {value : Foundation}
    (entry : PV_STX2_Source7EntryReferenceValid.FoundationConstructionEntryObligation''''' s value) :
    Source7EntryOwned'' s value :=
  PV_STX2_Source7EntryOwnedIndexed.forget entry.previous.previous

/-- Necessity prevents this adapter silently strengthening the provider's
caller obligation. Proof irrelevance keeps the same selected ownership witnesses. -/
theorem necessary {s : OWNER} {value : Foundation}
    (old : Source7EntryOwned'' s value)
    (entry : PV_STX2_Source7EntryReferenceValid.FoundationConstructionEntryObligation''''' s value) :
    CallerClauses old := by
  exact ⟨entry.previous.previous.registered,entry.nonnull,entry.previous.aligned,entry.bounded⟩

theorem exact_obligation {s : OWNER} {value : Foundation}
    (entry : Source7EntryOwned'' s value) :
    CallerClauses entry ↔
      PV_STX2_Source7EntryReferenceValid.FoundationConstructionEntryObligation''''' s value :=
  ⟨discharge entry,necessary entry⟩

/-- No in-run premise: column validity is projected from the discharged
entry obligation, on its original selected source header. -/
theorem column {s : OWNER} {value : Foundation}
    (entry : Source7EntryOwned'' s value) (clauses : CallerClauses entry)
    (i : Fin value.c1.val.length) :
    let h := PV_STX2_Source7EntrySelection.header entry.registered.owned i
    h.pointer ≠ 0 ∧ h.pointer % 4 = 0 ∧ h.pointer + (values value i).length*4 ≤ 2^64 :=
  PV_STX2_Source7EntryReferenceValid.column (discharge entry clauses) i

#print axioms discharge
#print axioms forget
#print axioms necessary
#print axioms exact_obligation
#print axioms column
end PV_LIB_SLICE_FoundationEntry
