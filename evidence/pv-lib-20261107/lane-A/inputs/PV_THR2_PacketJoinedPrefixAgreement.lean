import PV_THR2_JoinedCertDescriptor
import PV_THR2_PacketJoinedTableAway
import PV_THR2_PacketJoinedRetained121
import PV_THR2_InterpreterAgreement
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketJoinedPrefixAgreement
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- INTERNAL local instance of the existing simultaneous agreement. Generated
prefix syntax supplies Clear; no agreement premise enters the original entry
or OwnInit theorem. Both handler stores remain arbitrary until the suffix run
fixes them to its actual constructor issuance and dereference store. -/
theorem at_state (B : Carrier OWNER Data)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (resources : Resources) (encode : Encode) (constructorStore derefStore : Store Data)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
    (clear : PV_THR2_JoinedCertDescriptor.Clear q) :
    PV_THR2_TableIntrinsic.Agree
      (PV_THR2_Source208Table.table (PV_THR2_PacketOriginalTable.retained fallback))
      (PV_THR2_PacketJoinedTable.table fallback) q ∧
    PV_THR2_InterpreterAgreement.NativeAgree H
      (PV_THR2_PacketJoinedHandler.handler B resources encode constructorStore derefStore shape H) q := by
  constructor
  · intro c running wait fn a args done waiting request
    obtain ⟨n124,n126,n222,n216,n218,n315,n217,n312,n313,n320,box⟩ :=
      clear c running wait fn a args waiting request
    exact (PV_THR2_PacketJoinedTableAway.at_request fallback fn n124 n126 n222
      n216 n218 n315 n217 n312 n313 n320
      (PV_THR2_PacketJoinedRetained121.child fallback fn)).symm
  · intro c running wait waiting
    apply Eq.symm
    apply PV_THR2_PacketJoinedHandlerAway.request
    intro fn a args request
    exact PV_THR2_JoinedCertDescriptor.native fn
      (clear c running wait fn a args waiting request).2.2.2
#print axioms at_state
end PV_THR2_PacketJoinedPrefixAgreement
