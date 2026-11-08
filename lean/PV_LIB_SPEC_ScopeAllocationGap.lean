import PV_LIB_SPEC_SparsePacketHandler
import PV_LIB_SPEC_ConcreteEntry
import PV_THR2_ScopeData
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ScopeAllocationGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
abbrev C := (PV_LIB_SPEC_Frozen.runtime PV_LIB_SPEC_ConcreteEntry.parameters).carrier
abbrev K := (PV_LIB_SPEC_Frozen.runtime PV_LIB_SPEC_ConcreteEntry.parameters).control
/-- Both concrete monomorphizations are sent to the SAME generic emitted body.
ScopeData must use40 bytes; Packet must use48 bytes in the adopted ELF. -/
theorem scope_body : PV_LIB_SPEC_Full.programs (PV_THR2_ScopeChildren.descriptor 25) =
    some PV_THR2_F124.live := rfl

def atomic (n : Nat) : Data := PV_FN_THREAD_f360Outcomes.atomicValue
  PV_LIB_SPEC_FrozenABI.atomicKind PV_LIB_SPEC_FrozenABI.unsafeCellKind n

theorem not_an_option (w : OWNER) :
    PV_LIB_SPEC_SparsePacketHandler.scopeWord C K w (atomic 0) = none := rfl

/-- The actual ScopeData field order is counter, panicked, thread. The sparse
Packet codec cannot interpret it, for ANY thread or panic constructor value.
This is a LOCAL source-association contradiction, not original-entry reachability
and not a negation of the full joint existential. -/
theorem scope_decode (w : OWNER) (thread panicked : Data) :
    PV_LIB_SPEC_SparsePacketHandler.decode C K w (atomic 1) (atomic 1)
      (PV_THR2_ScopeData.value (atomic 0) thread panicked) = none := by
  change (do
    let result ← C.field panicked 0
    if K.variant result = some 0 then
      PV_LIB_SPEC_SparsePacketHandler.scopeWord C K w (atomic 0) else none) = none
  rw [not_an_option]
  cases h : C.field panicked 0 <;> simp [h]

/-- The Packet handler's installed layout is48, while the earlier ScopeData
instantiation in this same body has40. No allocator reply can identify these
requests; redefining the scope payload as a Packet would change source data. -/
theorem wrong_layout : PV_LIB_SPEC_SparseArc.shape.width ≠ 40 := by decide

#print axioms C
#print axioms K
#print axioms scope_body
#print axioms atomic
#print axioms not_an_option
#print axioms scope_decode
#print axioms wrong_layout
end PV_LIB_SPEC_ScopeAllocationGap
