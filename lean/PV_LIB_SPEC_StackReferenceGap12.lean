import PV_LIB_SPEC_NativeRecheck12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_StackReferenceGap12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen
/-- A valid initialized STACK source cell, admitted by Frozen.References,
is not necessarily a registered heap backing. No original reachability is
asserted for this local test activation. -/
def address : Address := ⟨7,50,[]⟩
def reference : Data := PV_STX2_TypedReferences.reference address .null
def store : Store Data := ⟨fun _ => some .null,8⟩
def before : OWNER := PV_LIB_SPEC_ConcreteCaptures.state
abbrev C := (runtime PV_LIB_SPEC_ConcreteEntry.parameters).carrier

theorem initialized : C.dereference before reference = some address ∧
    readAddress C store address = some .null := ⟨rfl,rfl⟩

theorem unregistered : receiver before ⟨7,[50]⟩ = none := rfl

theorem physical_missing :
    PV_LIB_SPEC_SparsePacketHandler.physical C before reference = none := rfl

/-- For EVERY k, source3472's field projections are well formed, yet the
old capture codec rejects the wrapper because it only knows heap registration.
This is SPEC-C10's LOCAL interface conflict, not a full OwnInit contradiction. -/
theorem capture_missing (k : Nat) :
    PV_LIB_SPEC_CallbackOperands.captureWords C before
      (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.maybeDangling
        [PV_THR2_KeyValues.pack
          (match PV_THR2_F15.node34 with | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null)
          [reference,.number k]]) = none :=
  PV_LIB_SPEC_CallbackOperands.missing_run _ _ _ _ _ physical_missing

#print axioms address
#print axioms reference
#print axioms store
#print axioms before
#print axioms initialized
#print axioms unregistered
#print axioms physical_missing
#print axioms capture_missing
end PV_LIB_SPEC_StackReferenceGap12
