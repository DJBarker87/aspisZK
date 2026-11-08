import PV_STX2_Source7ReadStores
import PV_STX2_Source7QBinding
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryOwnedRegistered
open PV_EVHB_OWNER PV_STX2_Source7EntryOwned
/-- Conditional on owner acceptance of the translator patch. Slice-4 refines
only the caller entry obligation: the entry region's heap address is registered
with the identity at the already selected entry place. -/
structure Source7EntryOwned' (s : OWNER) (value : Foundation) : Prop where
  owned : Source7EntryOwned s value
  registered : s.places (PV_STX2_Source7QBinding.ownerPlace
      (PV_STX2_Source7ReadStores.heapAddress owned)) =
    s.places (PV_STX2_Source7EntrySelection.place owned
      (PV_STX2_Source7EntryAddress.first value))
/-- Conditional on owner acceptance of the translator patch. Every earlier
slice theorem is consumed through this implication, without re-proof. -/
theorem forget {s : OWNER} {value : Foundation} (entry : Source7EntryOwned' s value) :
    Source7EntryOwned s value := entry.owned
/-- Conditional on owner acceptance of the translator patch. The refined
obligation belongs to the same Foundation-construction caller slice. -/
def FoundationConstructionEntryObligation' (s : OWNER) (value : Foundation) : Prop :=
  Source7EntryOwned' s value
/-- Conditional on owner acceptance of the translator patch. Resolve the
entry heap address by its new registration clause BY NAME. -/
theorem registered_receiver {s : OWNER} {value : Foundation} (entry : Source7EntryOwned' s value) :
    receiver s (PV_STX2_Source7QBinding.ownerPlace
      (PV_STX2_Source7ReadStores.heapAddress entry.owned)) =
    some (PV_STX2_Source7EntrySelection.identity entry.owned (PV_STX2_Source7EntryAddress.first value),
      PV_STX2_Source7EntrySelection.header entry.owned (PV_STX2_Source7EntryAddress.first value)) := by
  change (s.places _).bind _ = _
  rw [entry.registered]
  exact PV_STX2_Source7EntrySelection.receiver entry.owned _
#print axioms Source7EntryOwned'
#print axioms forget
#print axioms FoundationConstructionEntryObligation'
#print axioms registered_receiver
end PV_STX2_Source7EntryOwnedRegistered
