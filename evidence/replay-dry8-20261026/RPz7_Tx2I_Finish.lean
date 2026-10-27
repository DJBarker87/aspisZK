import RPz7_Tx2I_Cuts
import FinT_Model
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2I_Finish
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable

/-- Actual successful TX2 calls, followed by FinT's unchanged named laws at
that returned state. No whole finish, header, or model-acceptance premise. -/
theorem accepted_finish {W : Type} (base : VTop_Stages.Ops) (ops : FinishOps W)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (accepted : VTop_Stages.verifier.candidate.tx2_authenticated
      (Tx2I_Install.stage base ops) D pub proof checkpoint hash none = ok (.Ok ())) :
    Tx2I_Install.shape proof = ok (.Ok .S2) ∧
    Op3I_Install.sourceBody proof = ok (.Ok .S2) ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf proof.val) = true ∧
    ∃ (p : verifier.Prepared) (saved : verifier.Accumulator)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator) (after : verifier.BatchedWeights)
      (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)
      (v : verifier.View),
      base.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,saved)) ∧
      base.op6 proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      base.op9 after returned.weights.deref = ok flushed ∧
      let a := {returned with weights := back flushed}
      (Tx2I_Install.stage base ops).op19 v p a none = ok (.Ok ()) ∧
      Port4D_FinishInstall.finish ops v p a none = ok (.Ok ()) ∧
      ∀ (alpha0 alpha1 : E)
    (r0 : RoundValues ops v.round0 alpha0 p.claim)
    (r1 : RoundValues ops v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair dot : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : ops.dot v.final_message a.weights.deref = ok (.Ok dot))
    (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input parsed q tr = some i) (hq : queries tr = some q)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (canonical_S3_S4_S5_S9 : ∀ x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs],
      CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x)
    (saved_ten : CheckpointBytes5Output.accumulator saved =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (twelve : CheckpointBytes5Output.accumulator a =
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q) 12 (CheckpointBytes5Output.accumulator saved)),
    decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows parsed q tr) i := by
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached
    (Tx2I_Install.stage base ops) D hash pub proof checkpoint none accepted
  obtain ⟨rfl,source,header⟩ := Tx2I_Install.shape_header proof variant shape
  obtain ⟨p,saved,g,geometry,pending,returned,after,flushed,back,v,hr,hq,hb,hf,hfinish⟩ :=
    Tx2I_Cuts.common_reached (Tx2I_Install.stage base ops) D hash pub proof checkpoint none common
  refine ⟨shape,source,header,p,saved,g,geometry,pending,returned,after,flushed,back,v,hr,hq,hb,hf,hfinish,hfinish,?_⟩
  intro alpha0 alpha1 r0 r1 weights alphas pair dot s2 ha0 ha1 hw has hp hd
    parsed q tr i hi hqueries read decoded pairing_S3_S5_S9 matches_S4_S7 semantic_S3_S9
    dot_S5 canonical_S3_S4_S5_S9 saved_ten twelve
  exact FinT_Model.finish_value ops v p _ saved alpha0 alpha1 r0 r1 weights alphas pair dot
    s2 ha0 ha1 hw has hp hd parsed q tr i hi hqueries read decoded pairing_S3_S5_S9
    matches_S4_S7 semantic_S3_S9 dot_S5 canonical_S3_S4_S5_S9 saved_ten twelve

#print axioms accepted_finish
#print accepted_finish
end AspisR1.Tx2I_Finish
end
