import PV_THR2_Packet59To81Parametric
import PV_THR2_InlineFinalStoreContinuation
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361After124
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- The caller resumes on the complete callee final store. No source cell,
including a returned activation's cells, is discarded. -/
def resume {W E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.State W E :=
  ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 59,loops := loops},parents,s⟩,w,es⟩,stack⟩
def after {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :=
  let q63 := PV_THR2_Source361Chain59To63.after B q
  let q64 := PV_THR2_Source361Full63.after B H q63
  let q70 := PV_THR2_Source361Chain64To70.after B q64
  let q71 := PV_THR2_Source361Full70.after B H q70
  let q76 := PV_THR2_Source361Chain71To76.after B q71
  let q77 := PV_THR2_Source361Aggregate76.after B q76
  PV_THR2_Source361Chain77To81.after B q77
/-- Source instructions only, between BODY124's return and BODY126's call.
Existing segments are consumed by name;360 and456 remain arbitrary full replies.
Their explicit argument-store effects must be joined separately before closure. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E)
    (child360 : P PV_THR2_Source361PacketChildren.fn63 = none)
    (child456 : P PV_THR2_Source361PacketChildren.fn70 = none) :
    ∃ n, PV_THR2_IntrinsicState.advance B K P H n q = after B H q :=
  PV_THR2_Packet59To81Parametric.run B K P H q child360 child456
/-- Uniform in the complete124 post-store and the lower caller stack.
This is a source continuation, not a proof of124 or of f361's final contract. -/
theorem on_final_store {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : W) (es : List E) (stack : List Config)
    (child360 : P PV_THR2_Source361PacketChildren.fn63 = none)
    (child456 : P PV_THR2_Source361PacketChildren.fn70 = none) :
    ∃ n, PV_THR2_IntrinsicState.advance B K P H n
      (resume s a parents loops w es stack) =
      after B H (resume s a parents loops w es stack) :=
  run B K P H _ child360 child456
#print axioms run
#print axioms on_final_store
end PV_FN_THREAD_f361After124
