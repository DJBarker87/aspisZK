import PV_THR2_Packet63To81
import PV_THR2_PacketMetadataChildRuns
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Packet63To81Run
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Finite composition of the retained source segments. Child resolution is
internal; no prefix exclusion certificate or interpreter change is needed. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q0 : PV_THR2_IntrinsicState.State W E)
    (child63 : P PV_THR2_Source361PacketChildren.fn63 = none)
    (child70 : P PV_THR2_Source361PacketChildren.fn70 = none) :
    let q1 := PV_THR2_Source361Full63.after B H q0
    let q2 := PV_THR2_Source361Chain64To70.after B q1
    let q3 := PV_THR2_Source361Full70.after B H q2
    let q4 := PV_THR2_Source361Chain71To76.after B q3
    let q5 := PV_THR2_Source361Aggregate76.after B q4
    let q6 := PV_THR2_Source361Chain77To81.after B q5
    ∃ n, PV_THR2_IntrinsicState.advance B K P H n q0 = q6 := by
  intro q1 q2 q3 q4 q5 q6
  refine ⟨PV_THR2_Source361Full63.steps B q0 + PV_THR2_Source361Chain64To70.steps B q1 +
    PV_THR2_Source361Full70.steps B q2 + PV_THR2_Source361Chain71To76.steps B q3 +
    PV_THR2_Source361Aggregate76.steps B q4 + PV_THR2_Source361Chain77To81.steps B q5,?_⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicComposition.advance_add,
    PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicComposition.advance_add,
    PV_THR2_IntrinsicComposition.advance_add,
    PV_THR2_PacketMetadataChildRuns.at63 B K P H q0 child63,
    PV_THR2_Source361Chain64To70.run,
    PV_THR2_PacketMetadataChildRuns.at70 B K P H q2 child70,
    PV_THR2_Source361Chain71To76.run,PV_THR2_Source361Aggregate76.run,
    PV_THR2_Source361Chain77To81.run]
#print axioms run
end PV_THR2_Packet63To81Run
