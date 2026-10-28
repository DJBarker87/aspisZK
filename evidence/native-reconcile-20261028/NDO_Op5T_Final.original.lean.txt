import Op5T_SuccessAccepted
import Op5T_SamePair
import Op5T_SelectedPaths
import Op5T_Tx2
import Op5T_Concrete
import Op3I_Cuts
import Tx2I_Finish
import Op3I_Accepted
import S2W_D189Consolidation
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op5T_Final
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Same accepted witnesses and all Tx2I conclusions, at the concrete batch
source in BOTH dictionaries. This theorem retains the predecessor's original
marks and is not yet its success-conditioned event/effect replacement. -/
theorem accepted_pair_claims_op5 {W A E M Cv F : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (port : ChildConeJoin E (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd)) (firstMarks : Op5T_Marks.FirstMarks port) (secondMarks : Op5T_Marks.SecondMarks port) :
    ∃ f s outer pre middle fs ss,
      SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) e1.first (e2.second secondSizes) saved f s ∧
      (let sdk := Op5T_SamePair.dictionary adapterOps ops stageBase finishOps B claimsStd
       let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk
       let currentD := AspisS6CurrentFirstInstallation.toDigest D
       ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
         (p1 : VTop_Stages.verifier.Prepared) (root1 : Array U8 32#usize),
         Op5T_Install.currentBatch Port4B_Install.leaves currentD f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
         Op5T_Install.stageBatch Port4B_Install.leaves D s.proof p1 root1 1#usize () = ok (.Ok ())) ∧
      (Tx2I_Install.shape s.proof = ok (.Ok .S2) ∧
    Op3I_Install.sourceBody s.proof = ok (.Ok .S2) ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf s.proof.val) = true ∧
    ∃ (p : AspisR1Stage2.verifier.Prepared) (saved : AspisR1Stage2.verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : AspisR1Stage2.verifier.BatchedWeights)
      (returned : AspisR1Stage2.verifier.Accumulator) (after : AspisR1Stage2.verifier.BatchedWeights)
      (flushed : Slice AspisR1Stage2.aspis_core.field.QM31)
      (back : Slice AspisR1Stage2.aspis_core.field.QM31 → alloc.vec.Vec AspisR1Stage2.aspis_core.field.QM31)
      (v : AspisR1Stage2.verifier.View),
      stageBase.op18 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd)) s.checkpoint s.proof s.pub .S2 () = ok (.Ok (p,saved)) ∧
      stageBase.op6 s.proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      stageBase.op9 after returned.weights.deref = ok flushed ∧
      let a := {returned with weights := back flushed}
      (Tx2I_Install.stage (Op5T_Concrete.stage stageBase) finishOps).op19 v p a none = ok (.Ok ()) ∧
      Port4D_FinishInstall.finish finishOps v p a none = ok (.Ok ()) ∧
      ∀ (alpha0 alpha1 : AspisR1Stage2.Stage2Finish.E)
    (r0 : RowFinish_Control.RoundValues finishOps v.round0 alpha0 p.claim)
    (r1 : RowFinish_Control.RoundValues finishOps v.round1 alpha1 r0.value)
    (weights : F) (alphas : Slice AspisR1Stage2.Stage2Finish.E) (pair dot : AspisR1Stage2.Stage2Finish.E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : finishOps.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1Stage2.Stage2Finish.E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : finishOps.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : finishOps.dot v.final_message a.weights.deref = ok (.Ok dot))
    (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (hi : OraclePortStoredDecisionDraftC4.input parsed q tr = some i) (hq : OraclePortSelectedDraft.queries tr = some q)
    (read : LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finishOps)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (OraclePortStoredDecisionDraftC4.typedRows parsed q tr) i.data)
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
    decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native finishOps) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish finishOps v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (OraclePortStoredDecisionDraftC4.typedRows parsed q tr) i) ∧
      ((RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd).op3 f.proof = ok (.Ok .S2) ∧
        Op3I_Install.sourceBody f.proof = ok (.Ok .S2) ∧
        OraclePortHeader.accepts (bytesOf f.proof.val) = true ∧
        Op3I_Cuts.frozenHeader (bytesOf f.proof.val) = some .S2) ∧
      S2W_ExpandedTrace.runExpanded (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) (children port)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) e1.first (e2.second secondSizes) saved
          {f with semantic := selectedPublic} s ∧
        ∃ (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
          (sem : r1_semantic.Verified Unit) (claimsPrefix : AspisR1PublicPreparation.r1_wire.Prefix),
          AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1 = ok (.Ok v) ∧
          (semanticBase (Op3I_Install.install (Op5T_Concrete.current ops)) (ClaimsUnrolledFinish.install claimsStd B)).op9
            (NativeBuffers.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (withValues (Op3I_Install.install (Op5T_Concrete.current ops))) nativeValues
              AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install claimsStd B))
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic
                (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
            v.semantic () none = ok (.Ok sem) ∧
          AspisR1PublicPreparation.PrefixAdapter.parseAccepted v.semantic = ok (.Ok claimsPrefix) ∧
          ClaimsUnrolledFinish.reference claimsStd claimsPrefix = ok (.Ok (retainedSem sem).claims)) ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd) decode H s.pub s.proof s.checkpoint →
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage stageBase) finishOps) (Op3I_Install.install (Op5T_Concrete.current ops)) B claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,remaining⟩ :=
    Op5T_SuccessAccepted.accepted_pair_claims_op5 L sdk copy std allocator
      e1 e2 w1 w2 admission1 admission2 adapterOps ops stageBase finishOps B claimsStd
      native1 native2 hashv extraction sha256 H p1 syscall program data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length port firstMarks secondMarks
  exact ⟨f,s,outer,pre,middle,fs,ss,cuts,
    Op5T_SamePair.batches adapterOps ops stageBase finishOps B claimsStd _ _ saved f s cuts,remaining⟩

#print axioms accepted_pair_claims_op5
#print accepted_pair_claims_op5
end AspisR1.Op5T_Final
end
