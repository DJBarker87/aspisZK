import PV_STX2_OwnerWellFormed
import PV_STX2_Source7EntryOwnedRegistered
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryOwnedWellFormed
open PV_EVHB_OWNER PV_STX2_Source7EntryOwned PV_STX2_Source7EntryOwnedRegistered
open PV_STX2_OwnerWellFormed
/-- Conditional on owner acceptance of the translator patch. Slice-5 carries
the OWNER model invariant at the mid-program slice entry. -/
structure Source7EntryOwned'' (s : OWNER) (value : Foundation) : Prop where
  registered : Source7EntryOwned' s value
  wellFormed : OwnerWellFormed s
/-- Conditional on owner acceptance of the translator patch. Earlier proofs
consume the old entry obligation through this implication. -/
theorem forget {s : OWNER} {value : Foundation} (entry : Source7EntryOwned'' s value) :
    Source7EntryOwned' s value := entry.registered
/-- Conditional on owner acceptance of the translator patch. The entry's
selected identity is strictly older than the next minted identity. -/
theorem entry_id_lt_next {s : OWNER} {value : Foundation} (entry : Source7EntryOwned'' s value) :
    PV_STX2_Source7EntrySelection.identity entry.registered.owned
      (PV_STX2_Source7EntryAddress.first value) < s.next := by
  exact entry.wellFormed _ _ (PV_STX2_Source7EntrySelection.selected entry.registered.owned _).1
/-- Conditional on owner acceptance of the translator patch. Minting cannot
reuse the entry region's identity. -/
theorem entry_id_ne_minted {s : OWNER} {value : Foundation} (entry : Source7EntryOwned'' s value) :
    PV_STX2_Source7EntrySelection.identity entry.registered.owned
      (PV_STX2_Source7EntryAddress.first value) ≠ s.next :=
  Nat.ne_of_lt (entry_id_lt_next entry)
#print axioms Source7EntryOwned''
#print axioms forget
#print axioms entry_id_lt_next
#print axioms entry_id_ne_minted
end PV_STX2_Source7EntryOwnedWellFormed
