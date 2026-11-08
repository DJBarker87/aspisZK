import PV_STX2_Source7EntryReferenceValid
import PV_STX2_OwnerAllocationReferenceValid
import PV_STX2_ToVecCallBytePost
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecCallReferenceEntry
open PV_EVHB_OWNER PV_EVHB_RawVecOwner PV_STX2_Store PV_STX2_Syntax
/-- Conditional on owner acceptance of the translator patch. B-y call-entry
Pre refines the same owned registered argument with LOG D918 reference validity.
Every field is supplied at call entry, never as a copy-site premise. -/
structure Pre (w : OWNER) (store : Store Data) (p : Address) (n : Nat)
    (region : Vec PV_OWN2_Codec.M31) (sid : Nat) (hs : Header) : Prop where
  previous : PV_STX2_ToVecCallBytePost.Pre w store p n region sid hs
  owner : PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed w store.nextActivation
  nonnull : hs.pointer ≠ 0
  aligned : hs.pointer % 4 = 0
  bounded : hs.pointer + n*4 ≤ 2^64
/-- Conditional on owner acceptance of the translator patch. Every source7
column supplies the same refinement, with the same caller construction obligation. -/
theorem column {w : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryReferenceValid.Source7EntryOwned''''' w value)
    (i : Fin value.c1.val.length) (store : Store Data)
    (wf : PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed w store.nextActivation) :
    Pre w store ⟨0,(PV_STX2_Source7EntrySelection.header entry.previous.previous.owned i).pointer,[]⟩
      (PV_STX2_Source7EntryOwned.values value i).length
      ⟨PV_STX2_Source7EntrySelection.place entry.previous.previous.owned i,
        PV_STX2_Source7EntryOwned.values value i⟩
      (PV_STX2_Source7EntrySelection.identity entry.previous.previous.owned i)
      (PV_STX2_Source7EntrySelection.header entry.previous.previous.owned i) :=
  ⟨PV_STX2_ToVecCallBytePost.raw (PV_STX2_ToVecCallEntryRegion.column
      entry.previous.previous i store wf.previous.previous),wf,
    entry.nonnull i,entry.previous.aligned i,entry.bounded i⟩
#print axioms Pre
#print axioms column
end PV_STX2_ToVecCallReferenceEntry
