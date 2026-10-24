import Port7CLEAN_Recovered
import Port7CLEAN_Carrier
import Port6AUTH_Native
import Port6AUTH_Frames
import Port6AUTH_WordStability
import Port5Q1_Complete
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_Accepted
open scoped BigOperators
open FS FS2 FS2.Duplex
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft OraclePortStoredDecisionDraftC4
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortStoredAdmissionC4 Port1_StoredCarrier
open Port5Q1_QueryPorts Port5Q1_Endpoint OraclePortAllSelectedRecoveryC6
attribute [local irreducible] LiteralByteProtocol.protocol FS2.Protocol.transcript
  OraclePortStoredDecisionDraftC4.typedRows
  originalWith canon Port1_StoredCarrier.lift Port6AUTH_Prefix.source BinCompiledRunWordStability.wordsFromRun
attribute [local irreducible] OraclePortCheckpointStateC3.advance QueryAccumulator.run22
  OraclePortCheckpointStateC3.write QueryResidualBridge.values QueryResidualBridge.basis

/-- Native batch authentication, both query blocks, native finish and the
actual first/full source carrier compose to terminal Checks. This is a
call-level source theorem: dynamic driver reach and oracle trace producers
remain explicit, not replaced by model acceptance. -/
theorem terminal_from_calls {Observer X : Type} (c : S2LeadInterface.Inputs Observer)
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
    (decoder : LiteralByteProtocol.Decoder) (rust : Verifier) (adversary : ByteProver) (Q : Nat)
    (hqueries : ∀ oracle : Bytes → State, (eval oracle adversary).1.length ≤ Q)
    (physical : Physical rust)
    (sourceCalls : ∀ oracle input, (eval oracle (rust input)).1.length ≤ 1161)
    (contains : ∀ b : Fin 2, ∀ x,
      Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed pm.queries
        c.nodes b.val Port4B_BatchJoin.initial)).1 x → Read (Port6AUTH_SourceCut.first rust adversary H).1 x)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (eval H (Port6AUTH_Prefix.source decoder rust adversary)).1)
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
    (trBinding : tr=Port6AUTH_Frames.reached decoder H (Port6AUTH_SourceCut.first rust adversary H).2.1.statement (Port6AUTH_SourceCut.first rust adversary H).2.1.proof)
    (parseReached : OraclePortStoredParserC4.parseReached stored tr=some parsed)
    (samplerContains : ∀ x, Read (eval H (RawCutProverCompiler.verifier decoder (fun _ _ => false)
      (Port6AUTH_SourceCut.first rust adversary H).2.1.statement (Port6AUTH_SourceCut.first rust adversary H).2.1.proof)).1 x → Read (Port6AUTH_SourceCut.first rust adversary H).1 x)
    (storedBinding : stored=(Port6AUTH_SourceCut.first rust adversary H).2.1.stored)
    (sourceInput : OraclePortStoredDecisionDraftC4.input parsed q tr=some i)
    (sourceQueries : queries tr=some q)
    {W : Type} (finishOps : AspisR1Stage2.Stage2Finish.FinishOps W)
    (v : verifier.View) (s2 : p.variant=.S2)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finishOps)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dot_S5 : ∀ actual, finishOps.dot v.final_message (materialize out22 flushed22).weights.deref=ok (.Ok actual) →
      CheckpointBytes5Output.ofE actual = ∑ l : Fin 64, i.data.f l * LiteralOpeningView.eK
        ((CheckpointBytes5Output.accumulator (materialize out22 flushed22)).weights l))
    (finishSuccess : Port4D_FinishInstall.finish finishOps v p (materialize out22 flushed22) none=ok (.Ok ())) :
    Nonempty (LiteralAcceptanceTerminal.Checks
      (eval H (Port6AUTH_Prefix.source decoder rust adversary)).2.1.1
      ((LiteralByteProtocol.protocol decoder).transcript H
        (eval H (Port6AUTH_Prefix.source decoder rust adversary)).2.1.1
        (eval H (Port6AUTH_Prefix.source decoder rust adversary)).2.1.2 33).rounds) := by
  let log := (Port6AUTH_SourceCut.first rust adversary H).1
  let transcriptPublic := (Port6AUTH_SourceCut.first rust adversary H).2.1.statement
  let transcriptProof := (Port6AUTH_SourceCut.first rust adversary H).2.1.proof
  have consistent := FS.eval_consistent H (OraclePortRuntimeBindingC7.originalWith rust (OraclePortStoredAdmissionC4.canon (lift adversary)))
  have bound := Port6AUTH_SourceCut.budget decoder rust adversary Q hqueries physical sourceCalls H
  have cleanFirst := Port6AUTH_SourceCut.clean_first decoder rust adversary (Q+1161) H clean
  obtain ⟨parseOK,wireStored,aligned⟩ := OraclePortStoredParserC4.parsed stored tr parsed parseReached
  have matching := read
  rw [trBinding] at matching aligned
  let frames := Port6AUTH_Frames.frames decoder H transcriptPublic transcriptProof
  let selectors := Port6AUTH_Frames.selectors
  have frameRead := Port6AUTH_Frames.read decoder H transcriptPublic transcriptProof log samplerContains
  have rootRead := Port6AUTH_Frames.targets decoder H transcriptPublic transcriptProof parsed q i.data matching aligned
  have auth := Port6AUTH_Native.authenticated c D hash H stored pub saved parsed facts wireStored parseOK
    binary occupied sibling leaf p6 batchPrepared batchAccumulator pm am fields modelRoots folded foldedInput
    reached native log (Q+1161) contains consistent bound cleanFirst frames selectors frameRead rootRead
  have indexed : ∀ pos, pos<22 → recovered log (frames 2) parsed 2 (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos) := by
    simpa only [queryBinding,show (2 : Fin 3).val=2 by decide] using auth 2
  have completed := Port5Q1_Complete.accepted base ops ports proof p a0 out10 out22 g obs geometry0 geometry1 b0 b10 b1 b12
    flushed10 flushed22 parsed q tr i prepare read wire proofLength
    (recovered log (frames 2) parsed 2) indexed geometryOps geometryCanonical domain multiply one inverse
    geometryCall0 geometryCall1 reserved initial pending0 calls0 flush0 pending1 calls1 flush1

  have maps := Port6AUTH_Compiler.maps_eq_builder decoder rust adversary H parsed samplerContains rootRead
  have stable := Port6AUTH_WordStability.words_stable decoder rust adversary H samplerContains
  have decoded : LiteralQueryRead.decode i.queryBytes=some q := by
    have fields := (input_fields parsed q tr i sourceInput).1
    simpa [queries,fields.2.1] using sourceQueries
  have typed := Port7CLEAN_Terminal.typed_of_finish finishOps v p (materialize out22 flushed22)
    parsed q tr i s2 read decoded pairing_S3_S5_S9 matches_S4_S7 semantic_S3_S9 dot_S5
    completed.2.2.1 finishSuccess
  have allIndexed : ∀ k : Fin 3, ∀ pos, pos<22 →
      recovered log (frames k) parsed k.val (index q k.val pos)=
        some (OraclePortPackedChoiceC4.payload parsed k.val pos) := by
    simpa only [queryBinding] using auth
  have terminal := Port7CLEAN_Recovered.of_typed tr parsed q i sourceQueries sourceInput typed log frames allIndexed
  rw [maps] at terminal
  have rawParsed : parse (Port6AUTH_SourceCut.first rust adversary H).2.1.stored=some parsed := by
    rw [←storedBinding]
    exact parseOK
  have rows := Port7CLEAN_Carrier.rows decoder rust adversary H parsed q rawParsed
  rw [trBinding] at terminal
  rw [rows] at terminal
  have pub : (eval H (Port6AUTH_Prefix.source decoder rust adversary)).2.1.1=
      (Port6AUTH_SourceCut.first rust adversary H).2.1.statement := by
    simp only [Port6AUTH_Prefix.source_eval,OraclePortFrozen2Join.annotatedWith_eval,view,enrich]
  change Nonempty (LiteralAcceptanceTerminal.Checks
    (((LiteralByteProtocol.protocol decoder).transcript H
      (Port6AUTH_SourceCut.first rust adversary H).2.1.statement
      (Port6AUTH_SourceCut.first rust adversary H).2.1.proof 33).statement) _) at terminal
  rw [Port7CLEAN_Carrier.transcript_statement] at terminal
  exact pub.symm ▸ terminal

#print axioms terminal_from_calls
end AspisR1.Port7CLEAN_Accepted
end
