import Port6AUTH_Native
import Port6AUTH_Frames
import Port5Q1_Complete
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Query
open FS FS2 FS2.Duplex
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft OraclePortStoredDecisionDraftC4
open Port5Q1_QueryPorts Port5Q1_Endpoint OraclePortAllSelectedRecoveryC6
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryAccumulator.run22
  OraclePortCheckpointStateC3.write QueryResidualBridge.values QueryResidualBridge.basis

/-- Concrete native indexed recovery supplies Q1's exact premise. The SAME
containing log, actual two batch calls and all existing local Q1 ports remain
visible. No all-H AcceptedRunJoin is used or concluded. -/
theorem accepted {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
    (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (stored pub saved : Bytes) (parsed : Parsed)
    (facts : S2LeadInterface.S2CallerFacts c (VTop_Checkpoint.digest D) hash H stored pub saved parsed)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary
      (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H binary occupied sibling leaf)
    (batchPrepared : Fin 2 → VTop_Stages.verifier.Prepared)
    (batchAccumulator : Fin 2 → AspisR1Stage2.verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : Fin 2 → QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : ∀ b, CheckpointBytes4SavedFields.BodyMatches (batchPrepared b) (batchAccumulator b) pm (am b))
    (modelRoots : ∀ k : Fin 2, pm.roots k=committedRoot parsed k.val)
    (folded : Fin 2 → Array U8 32#usize)
    (foldedInput : ∀ b, bytesOf (folded b).val=bytes (committedRoot parsed 2))
    (reached : ∀ b : Fin 2, c.reached (Port4B_CallerJoin.site (Usize.ofNat b.val (by scalar_tac))))
    (native : ∀ b : Fin 2, Port4B_Install.batch D
      (c.proof (Port4B_CallerJoin.site (Usize.ofNat b.val (by scalar_tac))))
      (batchPrepared b) (folded b) (Usize.ofNat b.val (by scalar_tac)) hash=ok (.Ok ()))
    (log : List (Bytes × State)) (Q : Nat)
    (contains : ∀ b : Fin 2, ∀ x,
      Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries
        c.nodes b.val Port4B_BatchJoin.initial)).1 x → Read log x)
    (consistent : ∀ x ∈ log, x.2=H x.1)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
 {CoreError : Type} (base : VTop_Stages.Ops) (ops : Ops) (ports : SessionAPrimitives ops)
    (proof : Slice U8) (p : verifier.Prepared) (a0 out10 out22 : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry0 geometry1 : verifier.QueryGeometry) (b0 b10 b1 b12 : verifier.BatchedWeights)
    (flushed10 flushed22 : Slice aspis_core.field.QM31)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (prepare : SessionAPrepare p i.data q (SelectedChallengeMap.rhoOf i.rho))
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some i.data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (geometryOps : Port3_NativeGeometryBody.Ops CoreError)
    (geometryCanonical : Port5Q1_GeometryCanonical.SessionAPrimitives geometryOps)
    (domain : Port5Q1_Domain.SessionADomain geometryOps)
    (multiply : geometryOps.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geometryOps.op7=ok (1#u32))
    (inverse : geometryOps.op11=Port4C_InverseExecution.inverse_owned)
    (geometryCall0 : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometryOps)
      p.queries 0#usize 10#usize=ok (.Ok geometry0))
    (geometryCall1 : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geometryOps)
      p.queries 10#usize 22#usize=ok (.Ok geometry1))
    (reserved : Bool)
    (initial : Port3_Initial.constructor reserved .S2=ok (.Ok a0))
    (pending0 : Port3_NativePendingInstall.source reserved a0.weights.deref=ok (.Ok b0))
    (calls0 : verifier.candidate.query_loop (Port4C_RowStd.install (install ops))
      proof p a0 g obs geometry0 b0 10#usize=ok (.Ok (out10,b10)))
    (flush0 : Port3_FlushInstall.flush b10 out10.weights.deref=ok flushed10)
    (pending1 : Port3_NativePendingInstall.source reserved (materialize out10 flushed10).weights.deref=ok (.Ok b1))
    (calls1 : verifier.candidate.query_loop (Port4C_RowStd.install (install ops))
      proof p (materialize out10 flushed10) g obs geometry1 b1 22#usize=ok (.Ok (out22,b12)))
    (flush1 : Port3_FlushInstall.flush b12 out22.weights.deref=ok flushed22)
    (queryBinding : pm.queries=q)
    (decoder : LiteralByteProtocol.Decoder) (transcriptPublic : LiteralTranscript.Public)
    (transcriptProof : LiteralProtocol.Proof)
    (trBinding : tr=Port6AUTH_Frames.reached decoder H transcriptPublic transcriptProof)
    (parseReached : OraclePortStoredParserC4.parseReached stored tr=some parsed)
    (samplerContains : ∀ x, Read (eval H (RawCutProverCompiler.verifier decoder (fun _ _ => false)
      transcriptPublic transcriptProof)).1 x → Read log x) :
    let model := OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q
    CheckpointBytes5Output.accumulator (materialize out10 flushed10)=(OraclePortCheckpointStateC3.write model).accumulator ∧
    CheckpointBytes5Output.accumulator (materialize out22 flushed22)=
      OraclePortCheckpointStateC3.advance model 12 (CheckpointBytes5Output.accumulator (materialize out10 flushed10)) ∧
    CheckpointBytes5Output.accumulator (materialize out22 flushed22)=OraclePortFrozen2.completeState i q ∧
    flushed10.val.length=64 ∧ flushed22.val.length=64 ∧ out10.next.val=10 ∧ out22.next.val=22 := by
  obtain ⟨parseOK,wireStored,aligned⟩ := OraclePortStoredParserC4.parsed stored tr parsed parseReached
  have matching := read
  rw [trBinding] at matching aligned
  let frames := Port6AUTH_Frames.frames decoder H transcriptPublic transcriptProof
  let selectors := Port6AUTH_Frames.selectors
  have frameRead := Port6AUTH_Frames.read decoder H transcriptPublic transcriptProof log samplerContains
  have rootRead := Port6AUTH_Frames.targets decoder H transcriptPublic transcriptProof parsed q i.data matching aligned
  have auth := Port6AUTH_Native.authenticated c D hash H stored pub saved parsed facts wireStored parseOK
    binary occupied sibling leaf p6 batchPrepared batchAccumulator pm am fields modelRoots folded foldedInput
    reached native log Q contains consistent bound clean frames selectors frameRead rootRead
  have indexed : ∀ pos, pos<22 → recovered log (frames 2) parsed 2 (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos) := by
    simpa only [queryBinding,show (2 : Fin 3).val=2 by decide] using auth 2
  exact Port5Q1_Complete.accepted base ops ports proof p a0 out10 out22 g obs geometry0 geometry1 b0 b10 b1 b12
    flushed10 flushed22 parsed q tr i prepare read wire proofLength
    (recovered log (frames 2) parsed 2) indexed geometryOps geometryCanonical domain multiply one inverse
    geometryCall0 geometryCall1 reserved initial pending0 calls0 flush0 pending1 calls1 flush1

#print axioms accepted
end AspisR1.Port6AUTH_Query
end
