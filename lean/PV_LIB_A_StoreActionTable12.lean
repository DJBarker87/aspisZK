import PV_LIB_A_StoreActionTable11
import PV_LIB_A_RangeTo270History12
import PV_LIB_A_RangeInvariant12
import PV_LIB_A_F6Constructors12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Public source-phase-aware PARTIAL prefix surface. The legacy v2 table is
unchanged. No destructor adequacy, whole-table adequacy or full original-entry
OwnInit/source7 joint witness follows from this alias. -/
abbrev PrefixState12 := SourceState

def v2PrefixStep12 := PV_LIB_A_DeferredActions.step

def v2PrefixAdvance12 := PV_LIB_A_PrefixMachine11.advance

def v2PrefixEntry12 (s : State) : PrefixState12 := ⟨s,none⟩

/-- The retained source phase is required on pending retries. Repeatedly
wrapping the projected base would discard that control history. -/
theorem prefix_step12 (C : Carrier PV_EVHB_OwnerMachine.OWNER PV_STX2_Syntax.Data)
    (K : PV_STX2_SliceMachine.Control)
    (P : PV_STX2_Syntax.Data → Option PV_STX2_SliceSyntax.Program)
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (H : Handler) (values : PV_THR2_SourceStoreLibrary.Values PV_EVHB_OwnerMachine.OWNER PV_RJ4IDB.NativeEvent)
    (s : PrefixState12) :
    v2PrefixAdvance12 C K P resources encode H values 1 s =
      v2PrefixStep12 C K P resources encode H values s := rfl

#check v2
#check PV_LIB_A_RangeTo270History12.history
#check PV_LIB_A_Post93Prefix12.retained
#check PV_LIB_A_RangeInvariant12.delivered
#check PV_LIB_A_F6History12.history
#check PV_LIB_A_F6Constructors12.counter
#check PV_LIB_A_F6Constructors12.panicked
#print axioms v2PrefixStep12
#print axioms v2PrefixAdvance12
#print axioms v2PrefixEntry12
#print axioms prefix_step12
end PV_LIB_StoreActionTable
