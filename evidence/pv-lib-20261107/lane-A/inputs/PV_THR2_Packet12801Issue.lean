import PV_THR2_Packet124CallData
set_option autoImplicit false
namespace PV_THR2_Packet12801Issue
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Exact source12801 move, before any child answer or body effect. -/
theorem operands {W : Type} (B : Carrier W Data) (s : Store Data) (a : Nat)
    (packet : Data) (w : W) (cell : s.cells ⟨a,18,[]⟩ = some packet) :
    PV_STX2_Store.operands B w a [.move (.local 18)] s =
      some ([packet],PV_THR2_Packet124CallData.moved s a) := by
  simp [PV_STX2_Store.operands,operand,PV_STX2_Store.read,readAddress,readFields,
    locate,writeAddress,cell,PV_THR2_Packet124CallData.moved]
/-- Actual call issuance retains the complete source-selected store. This is
an internal reached configuration lemma; the caller supplies the derived cell. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (packet : Data) (w : W) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,18,[]⟩ = some packet)
    (resolved : P PV_THR2_Source361PacketChildren.fn58 = some PV_THR2_F124.live) :
    PV_THR2_IntrinsicState.advance B K P H 2
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 58,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_THR2_Packet124CallData.entered s a parents loops packet),w,es⟩,stack⟩ := by
  change PV_THR2_IntrinsicState.advance B K P H 2
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.node70 :: PV_THR2_F361.live.body.drop 59,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  have selected := operands B s a packet w cell
  have source := PV_THR2_IntrinsicStructuredCall.run B K P H s a parents loops
    (PV_THR2_F361.live.body.drop 59) PV_THR2_PacketEnter124.source.1
    PV_THR2_PacketEnter124.source.2.1 PV_THR2_PacketEnter124.source.2.2.1
    [.move (.local 18)] 17 PV_THR2_F124.live w es stack (by rfl)
    (by
      intro t vs
      apply PV_THR2_IntrinsicFrameOrdinary.run
      intro same
      have ids := congrArg PV_THR2_OffPath.functionId same
      cases ids) resolved
  simpa only [PV_THR2_IntrinsicStructuredCall.steps,PV_THR2_IntrinsicStructuredCall.after,
    selected,PV_THR2_Packet124CallData.entered,PV_THR2_PacketEnter124.source,
    PV_THR2_F361.node70,PV_THR2_Source361PacketChildren.fn58] using source
#print axioms operands
#print axioms run
end PV_THR2_Packet12801Issue
