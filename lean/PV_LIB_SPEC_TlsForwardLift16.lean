import PV_LIB_SPEC_TlsForward16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsForwardLift16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
theorem clear (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) (value pointer : Data)
    (cell : s.cells ⟨a,4,[]⟩ = some value)
    (variant : (runtime p).control.variant value = some 0)
    (field : (runtime p).carrier.field value 0 = some pointer) :
    ∀ k, k<7 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 24},parents,s⟩,w,es⟩) := by
  intro k hk
  interval_cases k <;>
    simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,PV_THR2_Execution.step,
      PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
      PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
      PV_STX2_SliceMachine.step,PV_THR2_Catch316Segment.select,
      PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node24,PV_THR2_F170.node41,PV_THR2_F170.block25,
      PV_THR2_F170.node42,PV_THR2_F170.node43,PV_THR2_F170.node44,PV_THR2_F170.node45,PV_THR2_F170.node46,native,adopt,PV_STX2_Native.step,
      PV_STX2_Store.bind,evaluate,operands,operand,PV_STX2_Store.read,locate,
      writeAddress,PV_STX2_Store.write,cell,variant,field,selectVariant]

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (value pointer : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,4,[]⟩ = some value)
    (variant : (runtime p).control.variant value = some 0)
    (field : (runtime p).carrier.field value 0 = some pointer) :
    PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 7
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 24},parents,s⟩,w,es⟩,[]⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 31},parents,
        PV_LIB_SPEC_TlsForward16.prepared s a pointer⟩,w,es⟩,[]⟩ := by
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _
    (clear p H s a parents w es value pointer cell variant field)]
  rw [PV_LIB_SPEC_TlsForward16.source _ _ _ _ _ value pointer _ _ cell variant field]

#print axioms clear
#print axioms source
end PV_LIB_SPEC_TlsForwardLift16
