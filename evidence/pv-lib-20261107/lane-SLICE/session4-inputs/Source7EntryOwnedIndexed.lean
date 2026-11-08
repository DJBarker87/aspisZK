import PV_STX2_Source7EntryOwnedWellFormed
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryOwnedIndexed
open PV_EVHB_OWNER PV_STX2_Source7EntryOwned
open PV_STX2_Source7EntryOwnedRegistered PV_STX2_Source7EntryOwnedWellFormed
/-- Conditional on owner acceptance of the translator patch. D812 extends the
slice-4 caller registration clause to every column; slice-5 is retained. -/
structure Source7EntryOwned''' (s : OWNER) (value : Foundation) : Prop where
  owned : Source7EntryOwned s value
  wellFormed : PV_STX2_OwnerWellFormed.OwnerWellFormed s
  registered : ∀ i : Fin value.c1.val.length,
    s.places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(PV_STX2_Source7EntrySelection.header owned i).pointer,[]⟩) =
    s.places (PV_STX2_Source7EntrySelection.place owned i)
/-- Conditional on owner acceptance of the translator patch. The first-column
registration is precisely the corresponding indexed instance. -/
theorem forget {s : OWNER} {value : Foundation} (entry : Source7EntryOwned''' s value) :
    Source7EntryOwned'' s value := by
  refine ⟨⟨entry.owned, ?_⟩, entry.wellFormed⟩
  exact entry.registered (PV_STX2_Source7EntryAddress.first value)
/-- Conditional on owner acceptance of the translator patch. The same
Foundation-construction obligation now supplies every address registration. -/
def FoundationConstructionEntryObligation''' (s : OWNER) (value : Foundation) : Prop :=
  Source7EntryOwned''' s value
#print axioms Source7EntryOwned'''
#print axioms forget
#print axioms FoundationConstructionEntryObligation'''
end PV_STX2_Source7EntryOwnedIndexed
