import Tx1Q_Execution
import Tx1Q_Initial
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Arithmetic
open AspisR1Stage2 Port3_NativeQueryBody Tx1Q_Carriers

/-- Canonicality follows along the actual successful calls, without any
parser, semantic matching, selected-map, or model-state equality premise. -/
theorem calls (ops : Ops) (arithmetic : Port4C_QueryArithmetic.SessionABackends ops)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
    (stop : Nat) (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n : Nat)
    (rho : Port3_FlushInstall.Canonical p.rho)
    (line : ∀ alpha values inverses value,
      ops.op16 alpha values inverses = ok value → Port4C_QueryArithmetic.CanonE value)
    (power : Port3_FlushInstall.Canonical a.power)
    (rhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (actual : Port2_QueryLoop.Calls
      (fun a b => verifier.candidate.query_values ops proof p a g obs geo b)
      stop a b out bout n) :
    Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  induction actual with
  | done => exact ⟨rhs,power⟩
  | step active returned tail ih =>
    obtain ⟨o,_,_,_,_,cr,cp⟩ := Port4C_QueryArithmetic.query ops arithmetic
      proof p _ _ g obs geo _ _ power rho rhs line returned
    exact ih cp cr

/-- The flushed writer state has the rhs returned by this query loop. -/
theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
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
  exact calls (Tx1Q_QueryBridge.leaves query) arithmetic proof (prepared run.p)
    (arr e run.scratch) none (geometry run.geometry) 10 _ _ _ _ _ rho
    ports.line_canonical init.2.2.1 init.2.2.2.1 actual

#print axioms calls
#print axioms on_run
end AspisR1.WAdm_Arithmetic
end
