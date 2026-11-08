import PV_STX2_Source7EntryOwnedIndexed
import PV_OWN2_Exports
import PV_STX2_OwnerReceiverPreservation
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7LoopInvariant
open PV_EVHB_OWNER PV_EVHB_RawVecOwner PV_STX2_Source7EntryOwned
open PV_STX2_Source7EntryOwnedIndexed PV_STX2_Source7EntrySelection
/-- Conditional on owner acceptance of the translator patch. Descriptors of
completed vectors are kept separately from the frozen entry descriptors. -/
structure ResultDescriptor where
  place : PV_EVHB_OWNER.Place
  identity : Nat
  header : Header
/-- Conditional on owner acceptance of the translator patch. Frame all entry
registrations, selected headers and complete entry regions, at fixed choices
made in the initial OWNER state. This is an invariant component, not a new
endpoint hypothesis. -/
structure EntryFrame {initial : OWNER} {value : Foundation}
    (entry : Source7EntryOwned''' initial value) (current : OWNER) : Prop where
  places : ∀ i : Fin value.c1.val.length,
    current.places (place entry.owned i) = initial.places (place entry.owned i)
  addresses : ∀ i : Fin value.c1.val.length,
    current.places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(header entry.owned i).pointer,[]⟩) =
    initial.places (PV_STX2_Source7QBinding.ownerPlace
      ⟨0,(header entry.owned i).pointer,[]⟩)
  headers : ∀ i : Fin value.c1.val.length,
    lookup current.world (identity entry.owned i) = some (header entry.owned i)
  bytes : ∀ (i : Fin value.c1.val.length) offset,
    offset < (header entry.owned i).cap * 4 →
    current.world.memory ((header entry.owned i).pointer + offset) =
    initial.world.memory ((header entry.owned i).pointer + offset)
/-- Conditional on owner acceptance of the translator patch. The requested
loop invariant: OWNER well-formedness; fixed entry frame; and every completed
column's live, distinct vector with its requested length and original bytes.
VecOwnership keeps every clause of the existing export. -/
structure Invariant (resources : Resources) (encode : Encode)
    {initial : OWNER} {value : Foundation} (entry : Source7EntryOwned''' initial value)
    (current : OWNER) (k : Nat)
    (results : Fin value.c1.val.length → ResultDescriptor) : Prop where
  bound : k ≤ value.c1.val.length
  wellFormed : PV_STX2_OwnerWellFormed.OwnerWellFormed current
  frame : EntryFrame entry current
  registered : ∀ i : Fin value.c1.val.length, i.val < k →
    receiver current (results i).place = some ((results i).identity,(results i).header)
  ownership : ∀ (i : Fin value.c1.val.length), i.val < k →
    ∀ granted : PV_OWN2_FreshAllocation.GrantedRegions,
      PV_OWN2_ExportContracts.VecOwnership (Attr := Unit) (Data := PV_STX2_Syntax.Data)
        (Native := Unit) (IoError := Unit) (OsString := Unit) (Scope := Unit)
        resources encode granted current ⟨place entry.owned i,values value i⟩
        (results i).place (identity entry.owned i) (results i).identity
        (header entry.owned i) (results i).header
  lengths : ∀ i : Fin value.c1.val.length, i.val < k →
    (results i).header.len = (values value i).length
  bytes : ∀ (i : Fin value.c1.val.length), i.val < k → ∀ offset,
    offset < (values value i).length * 4 →
    current.world.memory ((results i).header.pointer + offset) =
    initial.world.memory ((header entry.owned i).pointer + offset)
  distinct : ∀ (i j : Fin value.c1.val.length), i.val < k → j.val < k → i ≠ j →
    (results i).identity ≠ (results j).identity
/-- Conditional on owner acceptance of the translator patch. The invariant's
entry frame holds before the first iteration, with no native reply premise. -/
theorem frame_initial {s : OWNER} {value : Foundation} (entry : Source7EntryOwned''' s value) :
    EntryFrame entry s := by
  refine ⟨fun _ => rfl,fun _ => rfl,?_,fun _ _ _ => rfl⟩
  exact fun i => (selected entry.owned i).2.1
/-- Conditional on owner acceptance of the translator patch. Establish the
loop invariant at zero completed columns. Output slots are unobserved here. -/
theorem initial (resources : Resources) (encode : Encode)
    {s : OWNER} {value : Foundation} (entry : Source7EntryOwned''' s value)
    (results : Fin value.c1.val.length → ResultDescriptor) :
    Invariant resources encode entry s 0 results := by
  refine ⟨Nat.zero_le _, entry.wellFormed, frame_initial entry, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h; exact False.elim (Nat.not_lt_zero _ h)
  · intro i h; exact False.elim (Nat.not_lt_zero _ h)
  · intro i h; exact False.elim (Nat.not_lt_zero _ h)
  · intro i h; exact False.elim (Nat.not_lt_zero _ h)
  · intro i j h; exact False.elim (Nat.not_lt_zero _ h)
#print axioms ResultDescriptor
#print axioms EntryFrame
#print axioms Invariant
#print axioms frame_initial
#print axioms initial
end PV_STX2_Source7LoopInvariant
