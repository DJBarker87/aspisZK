import PV_LIB_SPEC_NativeKinds
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AtomicBoolGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_LIB_SPEC_ScopeAllocationGap
/-- AtomicBool's v.value is u8 in pinned Rust, and lane A's actual v2 load129
reads number0/1, then returns bool. Session11's ScopeData image requires a
boolean in that SAME storage cell, so the source-correct initial u8 is rejected.
This is a LOCAL interface mismatch, not original-entry reachability. -/
def zero (kind cellKind : Data) : Data :=
  PV_THR2_KeyValues.pack kind [PV_THR2_KeyValues.pack cellKind [.number 0]]

theorem numeric_rejected (w : OWNER) (thread kind cellKind : Data) :
    PV_LIB_SPEC_WordThreadArc.scopeWord C w
      (PV_THR2_ScopeData.value (atomic 0) thread (zero kind cellKind)) = none := rfl

/-- The rejection occurs before interpreting Thread, for EVERY native word. -/
theorem image_rejected (w : OWNER) (thread kind cellKind : Data) :
    PV_LIB_SPEC_WordThreadArc.image C K w .scope (atomic 1) (atomic 1)
      (PV_THR2_ScopeData.value (atomic 0) thread (zero kind cellKind)) = none := rfl

#print axioms zero
#print axioms numeric_rejected
#print axioms image_rejected
end PV_LIB_SPEC_AtomicBoolGap
