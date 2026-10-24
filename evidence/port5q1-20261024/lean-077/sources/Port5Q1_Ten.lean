import Port5Q1_QueryBlock
import Port5Q1_InitialFields
import Port5Q1_Recurrence
import Port5Q1_Materialize
import Port5Q1_AdvanceRange
import Port5Q1_InitialState
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Ten
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryResidualBridge.values QueryResidualBridge.basis

theorem accepted (base : VTop_Stages.Ops) (ops : Ops) (ports : SessionAPrimitives ops)
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
    (geo : Port5Q1_GeometryBinding.Binding p.queries 0#usize 10#usize geometry)
    (reserved : Bool)
    (initial : Port3_Initial.constructor reserved .S2=ok (.Ok a))
    (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
    (accepted : verifier.candidate.query_loop (Port4C_RowStd.install (install ops))
      proof p a g obs geometry b 10#usize=ok (.Ok (out,bout)))
    (flushed : Slice aspis_core.field.QM31)
    (flush : Port3_FlushInstall.flush bout out.weights.deref=ok flushed) :
    CheckpointBytes5Output.accumulator {out with weights:=⟨flushed.val,flushed.property⟩}=
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model data rho q)).accumulator ∧
      flushed.val.length=64 ∧ out.next.val=10 ∧
      Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  have init := Port5Q1_InitialFields.accepted base reserved a initial
  have block := Port5Q1_QueryBlock.materialized ops ports proof p a out g obs geometry b bout
    parsed q tr data rho prepare read wire proofLength recovered authenticated 0#usize 10#usize geo
    init.2.1 init.1 init.2.2.1 init.2.2.2.1 reserved pending accepted flushed flush
  refine ⟨?_,block.2⟩
  rw [init.2.2.2.2] at block
  exact block.1.trans (Port5Q1_Recurrence.ten _)

#print axioms accepted
end AspisR1.Port5Q1_Ten
end
