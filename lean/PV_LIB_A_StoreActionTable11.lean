import PV_LIB_A_RangeLegacy11
import PV_LIB_A_F6EarlyHistory11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Public source-phase-aware PARTIAL prefix surface. The legacy v2 table is
unchanged. No destructor adequacy, whole-table adequacy or full original-entry
OwnInit/source7 joint witness follows from this alias. -/
abbrev PrefixState11 := SourceState

def v2PrefixStep11 := PV_LIB_A_DeferredActions.step

def v2PrefixAdvance11 := PV_LIB_A_PrefixMachine11.advance

def v2PrefixEntry11 (s : State) : PrefixState11 := ⟨s,none⟩

/-- The retained source phase is required on pending retries. Repeatedly
wrapping the projected base would discard that control history. -/
theorem prefix_step11 (C : Carrier PV_EVHB_OwnerMachine.OWNER PV_STX2_Syntax.Data)
    (K : PV_STX2_SliceMachine.Control)
    (P : PV_STX2_Syntax.Data → Option PV_STX2_SliceSyntax.Program)
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (H : Handler) (values : PV_THR2_SourceStoreLibrary.Values PV_EVHB_OwnerMachine.OWNER PV_RJ4IDB.NativeEvent)
    (s : PrefixState11) :
    v2PrefixAdvance11 C K P resources encode H values 1 s =
      v2PrefixStep11 C K P resources encode H values s := rfl

#check v2
#check PV_LIB_A_RangeFirst11.history
#check PV_LIB_A_RangeRetry11.pending_retry
#check PV_LIB_A_RangeLegacy11.initial_poll
#check PV_LIB_A_F6EarlyHistory11.history
#print axioms v2PrefixStep11
#print axioms v2PrefixAdvance11
#print axioms v2PrefixEntry11
#print axioms prefix_step11
end PV_LIB_StoreActionTable
