import PV_LIB_SPEC_SourceNative12
import PV_LIB_SPEC_LocalOwnership
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_StackRecheck12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
open PV_LIB_SPEC_PhysicalStack12
def wrapped (k : Nat) : Data :=
  PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.maybeDangling
    [PV_THR2_KeyValues.pack
      (match PV_THR2_F15.node34 with | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null)
      [PV_LIB_SPEC_StackReferenceGap12.reference,.number k]]
def packet : Data := PV_THR2_KeyValues.pack .null
  [PV_THR2_KeyValues.pack .null
    [PV_STX2_TypedReferences.reference
      (PV_THR2_PacketBoxBacking.root PV_LIB_SPEC_LocalOwnership.allocationStore) .null]]
def before : OWNER := installDefault localFrame PV_LIB_SPEC_LocalOwnership.allocated

/-- SAME local stack map on a world with a real named
allocation/backing. Neither a fabricated registry slot for &run nor a decode
success premise is supplied. -/
theorem source_reference :
    physical localFrame PV_LIB_SPEC_StackReferenceGap12.C localConfig before
      PV_LIB_SPEC_StackReferenceGap12.reference = some 112 := by
  have deref : PV_LIB_SPEC_StackReferenceGap12.C.dereference before
      PV_LIB_SPEC_StackReferenceGap12.reference = some PV_LIB_SPEC_StackReferenceGap12.address := by
    rfl
  unfold physical
  simp only [localFrame,localConfig,ne_eq,not_true_eq_false,if_false]
  rw [deref]
  change (if PV_LIB_SPEC_StackReferenceGap12.address = PV_LIB_SPEC_StackReferenceGap12.address
    then some 112 else PV_LIB_SPEC_SparsePacketHandler.physical
      PV_LIB_SPEC_StackReferenceGap12.C before PV_LIB_SPEC_StackReferenceGap12.reference) = some 112
  exact if_pos rfl

/-- Actual local source projections close, including registered allocation8192
and unregistered source-stack &run112. Packet is a value-projection fixture;
no source type, original-entry or Packet-allocation provenance is claimed. -/
theorem operands (k : Nat) :
    registers localFrame PV_LIB_SPEC_ConcreteEntry.parameters localConfig before (wrapped k) packet =
      some ⟨32768,8192,112,k⟩ := by
  have ptr : PV_LIB_SPEC_CallbackSource.packetWord
      (runtime PV_LIB_SPEC_ConcreteEntry.parameters).carrier before packet = some 8192 := by
    rfl
  have cap : captureWords localFrame PV_LIB_SPEC_ConcreteEntry.parameters localConfig before (wrapped k) =
      some (112,k) := by
    change (do let pointer ← physical localFrame PV_LIB_SPEC_StackReferenceGap12.C localConfig before
                  PV_LIB_SPEC_StackReferenceGap12.reference
               pure (pointer,k)) = _
    rw [source_reference]
    rfl
  unfold registers
  rw [ptr,cap]
  rfl

/-- At the REAL callback token13923 the initialized suffix is now selected;
all operands are derived above, not assumed to decode successfully. This is
LOCAL, not a continuous original-entry history or allocation branch. -/
theorem callback (k : Nat) (hooks : Data) :
    PV_LIB_SPEC_StackCallback12.native localFrame
      {PV_LIB_SPEC_ConcreteEntry.parameters with resources := PV_LIB_SPEC_SuccessResources.callbackResources}
      localConfig
      (.child PV_THR2_Source361BoxTable.fnClosureBoxFull 8
        [PV_LIB_SPEC_CallbackNativeGap.payload (wrapped k) hooks packet]) before =
      some (PV_LIB_SPEC_CallbackStores.reply PV_LIB_SPEC_SuccessResources.callbackResources
        PV_LIB_SPEC_ConcreteEntry.parameters.encode {localConfig.store with nextActivation := 8}
        ⟨32768,8192,112,k⟩ before) := by
  rw [PV_LIB_SPEC_StackCallback12.at_call _ _ _ _ _ _ _ _ 8192
    (PV_LIB_SPEC_SuccessResources.local_callback _) (by decide)]
  rw [show registers localFrame
      {PV_LIB_SPEC_ConcreteEntry.parameters with resources := PV_LIB_SPEC_SuccessResources.callbackResources}
      localConfig before (wrapped k) packet = some ⟨32768,8192,112,k⟩ from operands k]
  rfl

#print axioms source_reference
#print axioms wrapped
#print axioms packet
#print axioms before
#print axioms operands
#print axioms callback
end PV_LIB_SPEC_StackRecheck12
