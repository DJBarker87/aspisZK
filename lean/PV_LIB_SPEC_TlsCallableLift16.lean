import PV_LIB_SPEC_TlsCallable16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsCallableLift16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
theorem clear (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) (fn actual : Data) (pointer : Address)
    (callable : s.cells ⟨a,2,[]⟩ = some fn)
    (reference : s.cells ⟨a,3,[]⟩ = some actual)
    (address : (runtime p).carrier.dereference w actual = some pointer) :
    ∀ k, k<9 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 31},parents,s⟩,w,es⟩) := by
  have ref : (runtime p).carrier.reference pointer .null = PV_STX2_TypedReferences.reference pointer .null := rfl
  have flag : (runtime p).carrier.constant PV_THR2_RunTlsCallable.literals.1 = some (.boolean false) := rfl
  have metadata : (runtime p).carrier.constant PV_THR2_RunTlsCallable.literals.2 = some .null := rfl
  have missing : (runtime p).carrier.aggregate PV_THR2_RunTlsCallable.descriptors.2
      [PV_STX2_TypedReferences.reference pointer .null] = none := rfl
  simp only [PV_THR2_RunTlsCallable.descriptors,PV_THR2_F170.node54] at missing
  simp only [PV_THR2_RunTlsCallable.literals,PV_THR2_F170.node49,PV_THR2_F170.node53] at flag metadata
  intro k hk
  interval_cases k <;>
    simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,PV_THR2_Execution.step,
      PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
      PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
      PV_STX2_SliceMachine.step,PV_THR2_Catch316Segment.select,
      PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node47,PV_THR2_F170.node48,PV_THR2_F170.node49,PV_THR2_F170.node50,PV_THR2_F170.node51,PV_THR2_F170.node52,PV_THR2_F170.node53,PV_THR2_F170.node54,native,adopt,PV_STX2_Native.step,
      PV_STX2_Store.bind,evaluate,operands,operand,PV_STX2_Store.read,locate,
      writeAddress,PV_STX2_Store.write,callable,reference,address,ref,flag,metadata,missing]

theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (fn actual : Data) (pointer : Address) (w : OWNER) (es : List Event)
    (callable : s.cells ⟨a,2,[]⟩ = some fn)
    (reference : s.cells ⟨a,3,[]⟩ = some actual)
    (address : (runtime p).carrier.dereference w actual = some pointer) :
    PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 9
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 31},parents,s⟩,w,es⟩,[]⟩ =
      ⟨⟨.running (PV_LIB_SPEC_TlsCallable16.config s a parents fn pointer),w,es⟩,[]⟩ := by
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _
    (clear p H s a parents w es fn actual pointer callable reference address)]
  rw [PV_LIB_SPEC_TlsCallable16.source _ _ _ _ _ fn actual pointer _ _ callable reference address]

#print axioms clear
#print axioms source
end PV_LIB_SPEC_TlsCallableLift16
