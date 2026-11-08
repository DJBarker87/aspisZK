import PV_LIB_A_StoreActionTable12
import PV_LIB_A_NextIteration13
import PV_LIB_A_F6IssuedHistory13
import PV_LIB_A_IntrinsicInvoke13
import PV_LIB_A_F316History13
import PV_LIB_A_CallNumbers13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- SAME partial phase-bearing machine as session12. This surface adds checked
prefix histories, not native/backend, physical-frame or whole-table adequacy.
Lane C's retained v2 cannot be silently replaced by projection of this state. -/
abbrev PrefixState13 := SourceState
abbrev v2PrefixStep13 := PV_LIB_A_DeferredActions.step
abbrev v2PrefixAdvance13 := PV_LIB_A_PrefixMachine11.advance

theorem prefix_step13 (C : Carrier PV_EVHB_OwnerMachine.OWNER Data)
    (K : Control) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : PV_EVHB_OwnerHeap.Resources) (encode : PV_EVHB_OwnerHeap.Encode)
    (H : Handler) (values : PV_THR2_SourceStoreLibrary.Values PV_EVHB_OwnerMachine.OWNER PV_RJ4IDB.NativeEvent)
    (s : PrefixState13) :
    v2PrefixAdvance13 C K P resources encode H values 1 s =
      v2PrefixStep13 C K P resources encode H values s := rfl

#check v2
#check PV_LIB_A_RangeIteration13.history
#check PV_LIB_A_NextIteration13.history
#check PV_LIB_A_CallFrame13.entered_iterator
#check PV_LIB_A_CallFrame13.returned_iterator
#check PV_LIB_A_F6IssuedHistory13.history
#check PV_LIB_A_IntrinsicInvoke13.actual
#check PV_LIB_A_F316History13.run
#print axioms v2PrefixStep13
#print axioms v2PrefixAdvance13
#print axioms prefix_step13
end PV_LIB_StoreActionTable
