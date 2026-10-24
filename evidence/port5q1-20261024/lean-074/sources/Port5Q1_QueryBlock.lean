import Port5Q1_Block
import Port5Q1_Materialize
import Port5Q1_AdvanceRange
import Port5Q1_InitialState
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_QueryBlock
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryResidualBridge.values QueryResidualBridge.basis

theorem materialized (ops : Ops) (ports : SessionAPrimitives ops)
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
      proof p a g obs geometry b end1=ok (.Ok (out,bout)))
    (flushed : Slice aspis_core.field.QM31)
    (flush : Port3_FlushInstall.flush bout out.weights.deref=ok flushed) :
    CheckpointBytes5Output.accumulator {out with weights:=⟨flushed.val,flushed.property⟩}=
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model data rho q)
        (end1.val-start.val) (CheckpointBytes5Output.accumulator a) ∧
      flushed.val.length=64 ∧ out.next.val=end1.val ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  obtain ⟨sum,trace,progress,state,next,weights,canonRhs,canonPower⟩ := Port5Q1_Block.loop
    ops ports proof p a out g obs geometry b bout parsed q tr data rho prepare read wire proofLength
    recovered authenticated start end1 geo beginning size hp hrhs reserved pending accepted
  have physical := Port5Q1_Materialize.exact (Port3_PendingInstall.owned a.weights.deref)
    out bout sum (OraclePortCheckpointResumeC5.model data rho q) (end1.val-start.val)
    (CheckpointBytes5Output.accumulator a) (by rw [weights]; exact size) trace progress state flushed flush
  exact ⟨physical.1,physical.2,next,canonRhs,canonPower⟩

#print axioms materialized
end AspisR1.Port5Q1_QueryBlock
end
