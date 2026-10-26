import RPz7_Tx1Q_Control
import RPz7_Tx1Q_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_Constructors
open Aeneas Aeneas.Std Result Tx1Q_Carriers

/-- Output property of the actual TX1 witness; not an admission hypothesis. -/
def Contents (initial : C.A) (state : C.B) : Prop :=
  (accumulator initial).weights.val = List.replicate 64 Port2_Initial.zeroK ∧
  (accumulator initial).rhs = Port2_Initial.zeroE ∧
  (accumulator initial).power = Port2_Initial.oneK ∧
  (accumulator initial).next = 0#usize ∧
  CheckpointBytes5Output.accumulator (accumulator initial) = QueryAccumulator.initial ∧
  (pending state).raw.val = (accumulator initial).weights.val.map Port3_PendingInstall.row ∧
  (pending state).terms = 0#usize ∧ (pending state).raw.val.length = 64

theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved) :
    Contents run.initial run.pending := by
  obtain ⟨_,weights,rhs,power,next⟩ := Tx1Q_Initial.raw reserved (accumulator run.initial) run.initial_call
  have fields := Tx1Q_Initial.fields reserved (accumulator run.initial) run.initial_call
  obtain ⟨_,rows,terms,size⟩ := Port3_NativePendingInstall.accepted_fields reserved
    (accumulator run.initial).weights.deref (pending run.pending) fields.1 run.pending_call
  exact ⟨weights,rhs,power,next,fields.2.2.2.2,rows,terms,size⟩

/-- Local constructor non-vacuity only, not a deployed accepted-pair fixture. -/
theorem local_nonvacuity : ∃ (a : C.A) (b : C.B),
    Tx1Q_PrefixInstall.initial true .S2 = ok (.Ok a) ∧
    Tx1Q_PrefixInstall.newPending true a.weights.deref = ok (.Ok b) :=
  Tx1Q_Nonvacuity.initial_pending

#print axioms on_run
#print axioms local_nonvacuity
end AspisR1.NP6_Constructors
end
