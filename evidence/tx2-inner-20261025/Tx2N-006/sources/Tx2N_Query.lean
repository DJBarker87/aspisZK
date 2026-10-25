import Tx2N_Fields
import Port5Q1_QueryBlock
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Query
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

theorem release_ports (ops : Port3_NativeQueryBody.Ops)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives ops) :
    Port5Q1_QueryPorts.SessionAPrimitives (Port3_QueryStage.release ops) :=
  ⟨⟨ports.basis.s3_s4_mul,ports.basis.s3_s4_sub,ports.basis.s3_s4_double,ports.basis.zero,ports.basis.one⟩,
   ⟨ports.arithmetic.s3_s4_s5_mulE,ports.arithmetic.s3_s4_s5_addE,ports.arithmetic.s3_s4_s9_mulK⟩,
   ⟨ports.m31.multiply,ports.m31.double,ports.m31.one,ports.m31.subtract⟩,
   ⟨ports.decoder.decode⟩,ports.line,ports.line_canonical⟩

/-- Source query and flush on their actual returned states. This local theorem
retains Q1's wire and indexed-authentication gates explicitly; the accepted-pair
consumer must derive them rather than passing a twelve-step state equation. -/
theorem twelve (ops : Port3_NativeQueryBody.Ops)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (saved returned : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geometry : verifier.QueryGeometry) (pending after : verifier.BatchedWeights)
    (flushed : Slice aspis_core.field.QM31)
    (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (rho : K) (c : Context)
    (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p saved (prepared c data rho q) am)
    (start : saved.next = 10#usize)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some data)
    (wire : parsed.wire = bytesOf proof.val) (proofLength : proof.val.length = 57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos < 22 → recovered (index q 2 pos) =
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (geo : Port5Q1_GeometryBinding.Binding p.queries 10#usize 22#usize geometry)
    (reserved : Bool)
    (hpending : Port3_NativePendingInstall.source reserved saved.weights.deref = ok (.Ok pending))
    (query : Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops))
      proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)))
    (mut : alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back))
    (flush : Port3_FlushInstall.flush after returned.weights.deref = ok flushed) :
    CheckpointBytes5Output.accumulator {returned with weights := back flushed} =
      OraclePortCheckpointStateC3.advance (model data rho q) 12
        (CheckpointBytes5Output.accumulator saved) := by
  obtain ⟨prepare,size,power,rhs⟩ := Tx2N_Fields.prepare p saved c data rho q am fields
  have native := (Port3_QueryInstall.success_iff _ _).mp query
  change Port3_NativeQueryBody.verifier.candidate.query_loop
    (Port4C_RowStd.install (Port5Q1_QueryPorts.install (Port3_QueryStage.release ops)))
    proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)) at native
  have exact := Port5Q1_QueryBlock.materialized (Port3_QueryStage.release ops) (release_ports ops ports)
    proof p saved returned g none geometry pending after parsed q tr data rho prepare read wire proofLength
    recovered authenticated 10#usize 22#usize geo (by rw [start]; rfl) size power rhs
    reserved hpending native flushed flush
  have backEq : back = fun s => (⟨s.val,s.property⟩ : alloc.vec.Vec aspis_core.field.QM31) :=
    (congrArg Prod.snd mut).symm
  rw [backEq]
  exact exact.1

#print axioms release_ports
#print axioms twelve
end AspisR1.Tx2N_Query
end
