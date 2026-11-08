import PV_STX2_Source7EntrySelection
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7EntryDescriptors
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_Syntax PV_STX2_Store PV_STX2_Source7EntryOwned PV_STX2_Source7EntrySelection
/-- Conditional on owner acceptance of the translator patch. A full header
base in the logical heap namespace; no equality search on pure values. -/
def pointer (h : Header) : Data :=
  PV_STX2_TypedReferences.reference ⟨0,h.pointer,[]⟩ .null
/-- Conditional on owner acceptance of the translator patch. Vec -> RawVec ->
RawVecInner -> Unique -> NonNull follows the four field-zero projections emitted
at f13/s535. Vec.len is field1 and RawVecInner.cap is retained separately.
This is a logical descriptor view, not a physical Rust layout theorem. -/
def descriptor (h : Header) : Data :=
  .array [.array [.array [.array [pointer h],.number h.cap]],.number h.len]
/-- Conditional on owner acceptance of the translator patch. Original entry
backing from the pre-state's selected headers in Foundation column order. -/
def foundation {s : OWNER} {value : Foundation} (entry : Source7EntryOwned s value) : Data :=
  PV_STX2_Aggregates.pack PV_STX2_SliceTypedEntry.foundationKind
    [.array (List.ofFn (fun i => descriptor (header entry i)))]
/-- Conditional on owner acceptance of the translator patch. The four emitted
field-zero projections select the pre-state header's full base. -/
theorem pointer_fields {W : Type} (base : Carrier W Data) (h : Header) :
    readFields (PV_STX2_SliceClonePointers.carrier base) [0,0,0,0] (descriptor h) =
      some (pointer h) := rfl
/-- Conditional on owner acceptance of the translator patch. Source Vec.len
comes from the header, never the pure column's second element. -/
theorem length_field {W : Type} (base : Carrier W Data) (h : Header) :
    readFields (PV_STX2_SliceClonePointers.carrier base) [1] (descriptor h) =
      some (.number h.len) := rfl
#print axioms pointer
#print axioms descriptor
#print axioms foundation
#print axioms pointer_fields
#print axioms length_field
end PV_STX2_Source7EntryDescriptors
