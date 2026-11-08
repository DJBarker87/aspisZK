import PV_LIB_SPEC_Tls278Trace15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls278Lift15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

def error : Data := PV_THR2_KeyValues.pack PV_THR2_RunTlsErrorCompleted.kind []
def config (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) : Config :=
  ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 21,waiting := some ⟨.child PV_THR2_RunTlsErrorCompleted.callee s.nextActivation [value,error],.child s.nextActivation (.local 5),[]⟩},
    parents,PV_THR2_RunTlsErrorCompleted.issued s a value error⟩

theorem clear (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) :
    ∀ k, k<4 → PV_THR2_IntrinsicTraceLift.Clear
      (PV_THR2_Execution.advance (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs H k
        ⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 17},parents,s⟩,w,es⟩) := by
  have missing : (runtime p).carrier.aggregate PV_THR2_RunTlsErrorCompleted.kind [] = none := rfl
  simp [PV_THR2_RunTlsErrorCompleted.kind,PV_THR2_F170.node19] at missing
  intro k hk
  interval_cases k <;>
    simp [PV_THR2_IntrinsicTraceLift.Clear,PV_THR2_Execution.advance,PV_THR2_Execution.step,
      PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,PV_THR2_GapCompletion.step,
      PV_THR2_AggregateCompletion.complete,PV_THR2_AggregateCompletion.carrier,
      PV_STX2_SliceMachine.step,PV_THR2_Catch316Segment.select,
      PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node17,
      PV_THR2_F170.node18,PV_THR2_F170.node19,native,adopt,PV_STX2_Native.step,
      PV_STX2_Store.bind,evaluate,operands,operand,PV_STX2_Store.read,locate,
      writeAddress,PV_STX2_Store.write,missing]

/-- The existing source4-step theorem supplies its final store and wait token.
The only new proof is the finite instruction-shape lift into intrinsic state. -/
theorem source (p : Parameters) (H : Handler) (s : Store Data) (a : Nat)
    (parents : List Frame) (value : Data) (w : OWNER) (es : List Event)
    (cell : s.cells ⟨a,6,[]⟩ = some value) :
    PV_THR2_IntrinsicState.advance (runtime p).carrier (runtime p).control
      PV_LIB_SPEC_Full.programs H 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 17},parents,s⟩,w,es⟩,[]⟩ =
      ⟨⟨.running (config s a parents value),w,es⟩,[]⟩ := by
  rw [PV_THR2_IntrinsicTraceLift.run _ _ _ _ _ _ _ (clear p H s a parents w es)]
  rw [PV_THR2_RunTlsErrorCompleted.request _ _ _ _ _ _ _ value _ _ cell
    (show (runtime p).carrier.aggregate PV_THR2_RunTlsErrorCompleted.kind [] = none from rfl)]
  rfl

theorem reached (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (value : Data) (w : OWNER)
    (es : List Event) (issued : List Issued) (consumed : List Context)
    (cell : s.cells ⟨a,6,[]⟩ = some value) :
    (PV_LIB_SPEC_ReachedNative14.run cut p 4
      (stage s a parents (PV_THR2_F170.live.body.drop 17) w es issued consumed)).state =
      ⟨⟨.running (config s a parents value),w,es⟩,[]⟩ :=
  PV_LIB_SPEC_SourceProjection15.transport cut p H _ _ _
    (PV_LIB_SPEC_Tls278Trace15.trace cut p H s a parents w es issued consumed)
    (source p H s a parents value w es cell)

#print axioms error
#print axioms config
#print axioms clear
#print axioms source
#print axioms reached
end PV_LIB_SPEC_Tls278Lift15
