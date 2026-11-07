import PV_THR2_JoinedCertChunk15
import PV_THR2_PacketJoinedPrefixAgreement
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_JoinedPrefix
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Retained resolver used only on the certified prefix. The target resolver
already executes124/126 from entry; no resolver is changed at a reached cut. -/
def retained (fallback : Data → Option PV_STX2_SliceSyntax.Program) :=
  PV_THR2_Source208Table.table (PV_THR2_PacketOriginalTable.retained fallback)
/-- One lift over an existing named source certificate. No native reply,
source store, caller suffix, branch or event prefix is restricted. -/
theorem lift {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (n : Nat) (q : PV_THR2_IntrinsicState.State OWNER E)
    (cert : PV_THR2_JoinedCertDispatchTrace.Certificate B K (retained fallback) H n q) :
    PV_THR2_IntrinsicState.advance B K (PV_THR2_PacketJoinedTable.table fallback) H n q =
      PV_THR2_IntrinsicState.advance B K (retained fallback) H n q := by
  apply PV_THR2_InterpreterAgreement.run
  intro k hk
  constructor
  · intro c running wait fn a args done waiting request
    obtain ⟨n124,n126,n222,n216,n218,n315,n217,n312,n313,n320,box⟩ :=
      cert k hk c running wait fn a args waiting request
    exact (PV_THR2_PacketJoinedTableAway.at_request fallback fn n124 n126 n222
      n216 n218 n315 n217 n312 n313 n320
      (PV_THR2_PacketJoinedRetained121.child fallback fn)).symm
  · intro c running wait waiting
    rfl
#print axioms lift
end PV_FN_THREAD_JoinedPrefix
