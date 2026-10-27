import Tx2N_Execution
import Tx2N_Query
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Twelve
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisR1Stage2.Stage2Finish
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

/-- Successful source TX2 supplies its own geometry/pending/query/flush calls.
The only arithmetic ports are the existing named Session A primitives. Wire
binding is by construction. Indexed packed recovery remains an explicit S1
gate; this theorem is not an unconditional discharge of that gate. -/
theorem accepted {CoreError W Hash : Type} (base : VTop_Stages.Ops) (finish : FinishOps W)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
    (domain : Port5Q1_Domain.SessionADomain geoOps)
    (multiply : geoOps.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geoOps.op7 = ok 1#u32)
    (inverse : geoOps.op11 = Port4C_InverseExecution.inverse_owned)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (same : bytesOf checkpoint.val = bytesOf savedVec.val)
    (success : VTop_Stages.verifier.candidate.tx2_authenticated
      (Tx2I_Install.stage (Tx2N_Execution.control base reserved queryOps geoOps) finish)
      D pub proof checkpoint hash none = ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (saved : verifier.Accumulator)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator) (after : verifier.BatchedWeights)
      (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
      (v : verifier.View),
      Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash = ok (.Ok (p,saved)) ∧
      Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install queryOps))
        proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      Port3_FlushInstall.flush after returned.weights.deref = ok flushed ∧
      Port4D_FinishInstall.finish finish v p {returned with weights := back flushed} none = ok (.Ok ()) ∧
      ∀ (semantic : List Bytes) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
        (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K) (c : Context),
        LiteralMatchingData.read (typedRows ⟨bytesOf proof.val,semantic⟩ q tr) = some data →
        ∀ recovered : Nat → Option Bytes,
        (∀ pos, pos < 22 → recovered (index q 2 pos) =
          some (OraclePortPackedChoiceC4.payload ⟨bytesOf proof.val,semantic⟩ 2 pos)) →
        (tx1_saved : savedVec = Tx2N_Reader.writer H stored publicBytes (prepared c data rho q)
          (OraclePortCheckpointStateC3.write (model data rho q)).accumulator) →
        CheckpointBytes5Output.accumulator saved = (OraclePortCheckpointStateC3.write (model data rho q)).accumulator ∧
        CheckpointBytes5Output.accumulator {returned with weights := back flushed} =
          OraclePortCheckpointStateC3.advance (model data rho q) 12 (CheckpointBytes5Output.accumulator saved) := by
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ D hash pub proof checkpoint none success
  obtain ⟨rfl,headerSource,header⟩ := Tx2I_Install.shape_header proof variant shape
  have size : proof.val.length = 57607 := by
    have len := (OraclePortHeader.accepts_iff _).mp header
    simpa only [bytesOf,List.length_map] using len.1
  have commonRun : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control (Tx2I_Install.stage base finish) reserved queryOps geoOps)
      D pub proof checkpoint hash none = ok (.Ok ()) := common
  obtain ⟨p,saved,g,geometry,pending,returned,after,flushed,back,v,
    hr,hnext,hg,hgeo,hpending,hquery,hback,hflush,hfinish⟩ :=
    Tx2N_Execution.common (Tx2I_Install.stage base finish) reserved queryOps geoOps D hash pub proof checkpoint commonRun
  refine ⟨p,saved,g,geometry,pending,returned,after,flushed,back,v,hr,hquery,hback,hflush,hfinish,?_⟩
  intro semantic q tr data rho c read recovered authenticated tx1_saved
  have savedFields := Tx2N_Reader.saved_ten base reserved queryOps D hash checkpoint proof pub savedVec
    p saved H stored publicBytes c data rho q same tx1_saved hr
  rw [hnext] at hgeo
  have geo := Port5Q1_GeometryReads.accepted geoOps geoLeaves domain multiply one inverse
    p.queries 10#usize 22#usize geometry (by decide) hgeo
  exact ⟨savedFields.2.1,Tx2N_Query.twelve queryOps queryLeaves proof p saved returned g geometry pending after
    flushed back ⟨bytesOf proof.val,semantic⟩ q tr data rho c _ savedFields.1 hnext read rfl size
    recovered authenticated geo reserved hpending hquery hback hflush⟩

#print axioms accepted
#print accepted
end AspisR1.Tx2N_Twelve
end
