import PV_THR2_Packet59To81Run
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Packet59To81Parametric
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Reuse the existing metadata composition with one supplied dispatch table
and handler. Only the two exact child dispositions are internal obligations.
No source step, original prefix, exception certificate or store is replayed. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E)
    (child63 : P PV_THR2_Source361PacketChildren.fn63 = none)
    (child70 : P PV_THR2_Source361PacketChildren.fn70 = none) :
    let q63 := PV_THR2_Source361Chain59To63.after B q
    let q64 := PV_THR2_Source361Full63.after B H q63
    let q70 := PV_THR2_Source361Chain64To70.after B q64
    let q71 := PV_THR2_Source361Full70.after B H q70
    let q76 := PV_THR2_Source361Chain71To76.after B q71
    let q77 := PV_THR2_Source361Aggregate76.after B q76
    let q81 := PV_THR2_Source361Chain77To81.after B q77
    ∃ n, PV_THR2_IntrinsicState.advance B K P H n q = q81 := by
  intro q63 q64 q70 q71 q76 q77 q81
  obtain ⟨n,suffix⟩ := PV_THR2_Packet63To81Run.run B K P H q63 child63 child70
  refine ⟨PV_THR2_Source361Chain59To63.steps B q + n,?_⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Chain59To63.run]
  exact suffix
#print axioms run
end PV_THR2_Packet59To81Parametric
