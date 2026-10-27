import Tx2N_Twelve
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Finish
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable

/-- Concrete inner arithmetic composition. No saved_ten/twelve state equation
is an input. Indexed packed recovery remains explicit, so this is not claimed
to discharge that source-to-S1 binding on the accepted SDK pair. -/
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
      let a := {returned with weights := back flushed}
      Port4D_FinishInstall.finish finish v p a none = ok (.Ok ()) ∧
      ∀ (alpha0 alpha1 : E)
    (r0 : RoundValues finish v.round0 alpha0 p.claim)
    (r1 : RoundValues finish v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair dot : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : finish.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : finish.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : finish.dot v.final_message a.weights.deref = ok (.Ok dot))
    (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr = some i) (hq : queries tr = some q)
    (read : LiteralMatchingData.read (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (canonical_S3_S4_S5_S9 : ∀ x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs],
      CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x)
    (c : Context) (recovered : Nat → Option Bytes)
    (authenticated_S1 : ∀ pos, pos < 22 → recovered (index q 2 pos) =
      some (OraclePortPackedChoiceC4.payload ⟨bytesOf proof.val,semantic⟩ 2 pos))
    (tx1_saved : savedVec = Tx2N_Reader.writer H stored publicBytes
      (prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator),
    decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native finish) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish finish v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i ∧
    D0TypedChecks.verify (typedRows ⟨bytesOf proof.val,semantic⟩ q tr) i = true := by
  obtain ⟨p,saved,g,geometry,pending,returned,after,flushed,back,v,hr,hquery,hback,hflush,hfinish,states⟩ :=
    Tx2N_Twelve.accepted base finish reserved queryOps queryLeaves geoOps geoLeaves domain multiply one inverse
      D hash pub proof checkpoint savedVec H stored publicBytes same success
  refine ⟨p,saved,g,geometry,pending,returned,after,flushed,back,v,hr,hquery,hback,hflush,hfinish,?_⟩
  intro alpha0 alpha1 r0 r1 weights alphas pair dot s2 ha0 ha1 hw has hp hd semantic q tr i hi hq read decoded
    pairing_S3_S5_S9 matches_S4_S7 semantic_S3_S9 dot_S5 canonical_S3_S4_S5_S9 c recovered authenticated_S1 tx1_saved
  obtain ⟨saved_ten,twelve⟩ := states semantic q tr i.data (SelectedChallengeMap.rhoOf i.rho) c
    read recovered authenticated_S1 tx1_saved
  have values := FinT_Model.finish_value finish v p _ saved alpha0 alpha1 r0 r1 weights alphas pair dot
    s2 ha0 ha1 hw has hp hd ⟨bytesOf proof.val,semantic⟩ q tr i hi hq read decoded pairing_S3_S5_S9
    matches_S4_S7 semantic_S3_S9 dot_S5 canonical_S3_S4_S5_S9 saved_ten twelve
  refine ⟨values.1,values.2,?_⟩
  rw [← values.2]
  simp only [hfinish,decide_true]

#print axioms accepted
#print accepted
end AspisR1.Tx2N_Finish
end
