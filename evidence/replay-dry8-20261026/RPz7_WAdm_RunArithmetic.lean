import RPz7_WAdm_Execution
import RPz7_WAdm_Arithmetic
import RPz7_Tx1Q_Initial
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_RunArithmetic
open AspisR1Stage2 Port3_NativeQueryBody Tx1Q_Carriers

/-- The flushed writer state has the rhs returned by this query loop. -/
theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : WAdm_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (rho : Port3_FlushInstall.Canonical (prepared run.p).rho) :
    Port4C_QueryArithmetic.CanonE (accumulator run.out).rhs ∧
    Port3_FlushInstall.Canonical (accumulator run.out).power := by
  have init := Tx1Q_Initial.fields reserved (accumulator run.initial) run.initial_call
  have arithmetic : Port4C_QueryArithmetic.SessionABackends (Tx1Q_QueryBridge.leaves query) :=
    ⟨ports.arithmetic.s3_s4_s5_mulE, ports.arithmetic.s3_s4_s5_addE,
      ports.arithmetic.s3_s4_s9_mulK⟩
  have h := run.query_call
  rw [Port3_NativeQueryFrame.loop_eq] at h
  have actual := Port2_QueryLoop.source_calls
    (Port3_NativeQueryBody.verifier.candidate.query_values (Tx1Q_QueryBridge.leaves query))
    proof (prepared run.p) (arr e run.scratch) none (geometry run.geometry) 10#usize
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (Tx1Q_QueryBridge.leaves query)
      proof (prepared run.p) a a1 (arr e run.scratch) none (geometry run.geometry) b b1 h).2.2)
    (accumulator run.initial) (accumulator run.out) (pending run.pending) (pending run.after)
    (by rw [init.2.1]; decide) h
  exact WAdm_Arithmetic.calls (Tx1Q_QueryBridge.leaves query) arithmetic proof (prepared run.p)
    (arr e run.scratch) none (geometry run.geometry) 10 _ _ _ _ _ rho
    ports.line_canonical init.2.2.1 init.2.2.2.1 actual

#print axioms on_run
end AspisR1.WAdm_RunArithmetic
end
