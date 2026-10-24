import Port5Q1_Observation
import Port5Q1_AdvanceRange
import Port5Q1_InitialState
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Block
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryResidualBridge.values QueryResidualBridge.basis

theorem loop (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data FE) (rho : FK)
    (prepare : SessionAPrepare p data q rho)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (start end1 : Usize) (geo : Port5Q1_GeometryBinding.Binding p.queries start end1 geometry)
    (beginning : a.next.val=start.val) (size : a.weights.val.length=64)
    (hp : Port3_FlushInstall.Canonical a.power) (hrhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (reserved : Bool)
    (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
    (accepted : verifier.candidate.query_loop (Port4C_RowStd.install (install ops))
      proof p a g obs geometry b end1=ok (.Ok (out,bout))) :
    ∃ sumOut,
      S7Kani3CallerTrace.PushTrace (Port3_PendingInstall.owned a.weights.deref) (Port3_RowsInstall.toBW bout) sumOut ∧
      S7JoinRowsTrace.Progress (end1.val-start.val) 0 (Port3_RowsInstall.toBW bout) ∧
      Port4C_QueryState.state out sumOut=OraclePortCheckpointStateC3.advance
        (OraclePortCheckpointResumeC5.model data rho q) (end1.val-start.val)
        (CheckpointBytes5Output.accumulator a) ∧
      out.next.val=end1.val ∧ out.weights=a.weights ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  have new := Port4C_Pending.accepted reserved a.weights.deref b size pending
  rw [Port3_NativeQueryFrame.loop_eq] at accepted
  have actual := Port2_QueryLoop.source_calls
    (verifier.candidate.query_values (Port4C_RowStd.install (install ops))) proof p g obs geometry end1
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (Port4C_RowStd.install (install ops))
      proof p a a1 g obs geometry b b1 h).2.2) a out b bout (by rw [beginning]; exact Nat.le_of_lt geo.order) accepted
  have installedPorts := Port5Q1_InstallPorts.installed ops ports
  obtain ⟨sumOut,trace,progress,state,canonRhs,canonPower⟩ := Port5Q1_AdvanceRange.calls
    (install ops) installedPorts.basis installedPorts.arithmetic (OraclePortCheckpointResumeC5.model data rho q)
    rfl (Port3_PendingInstall.owned a.weights.deref) proof p prepare.rho_eq.symm g obs geometry start.val end1.val
    (fun a a1 b b1 lo hi returned o => by
      have fields := Port5Q1_Observation.fields ops ports proof p a a1 g obs geometry b b1
        parsed q tr data rho prepare read wire proofLength recovered authenticated start end1 geo lo hi o
      exact ⟨fields.2.1,fields.2.2⟩)
    a out b bout (end1.val-a.next.val) 0 (S7Kani3CallerTrace.initialSum (Port3_PendingInstall.owned a.weights.deref))
    size (by omega) (by have := geo.bound; omega) hp prepare.rho_canonical hrhs installedPorts.line_canonical
    new.2.2.2.2.1 new.2.2.2.2.2 actual
  have weights := Port3_QueryFrame.calls_weights _ _ _ _ _ _ _
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (Port4C_RowStd.install (install ops))
      proof p a a1 g obs geometry b b1 h).2.1) actual
  refine ⟨sumOut,trace,?_,?_,Port2_QueryLoop.returned_next _ _ _ _ _ _ _ actual,weights,canonRhs,canonPower⟩
  · simpa only [Nat.zero_add,beginning] using progress
  · rw [beginning,Port5Q1_InitialState.state a size] at state
    exact state

#print axioms loop
end AspisR1.Port5Q1_Block
end
