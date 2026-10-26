import RPz7_CPhy_Header
import RPz7_CPhy_Ranges
import RPz7_CPhy_Accepted
import RPz7_WAdm_NativeEndpoint
import RPz7_SdkD_Accepted
import RPz7_SdkD_Inner
import RPz7_SdkD_Uni
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.CPhy_Physical
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted_pair_unified {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) native1 native2 hashv)
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
    :
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps B claimsStd
    ∃ f s outer pre middle fs ss,
      SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) e1.first (e2.second secondSizes) saved f s ∧
      CheckpointWriterConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) CPhy_Header.decode H f.semantic f.pub f.proof f.split ∧
      CheckpointReaderConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) CPhy_Header.decode H s.pub s.proof s.checkpoint ∧
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof (CPhy_Ranges.nodes f.proof s.proof) ∧
      S2W_ChildJoins.S8StageConeJoin f.proof (CPhy_Ranges.y1 f.proof) ∧
      Op4P_Extract.Op4P_reference.reference.check_values (CPhy_Ranges.y1 f.proof) = ok true ∧
      ((RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved queryOps geoOps) B claimsStd).op4 f.proof = ok (.Ok ()) ∧
        Op4P_Install.sourceBody f.proof = ok (.Ok ()) ∧
        OraclePortCompactDraft.scan (bytesOf f.proof.val)) ∧
      (∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
        reserved queryOps geoOps (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd) ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
        reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
        (∀ x ∈ (Tx1Q_Carriers.slice Tx1Q_Carriers.k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
        Port3_CheckpointInstall.writer
          (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd))
          (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
          f.proof f.pub () = ok saved ∧
        WAdm_Domain.Admitted (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ∧
        WAdm_Carrier.WideInputs (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) ∧
        WAdm_SourceWriter.writer (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd))
          (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
          f.proof f.pub () = ok saved ∧
        (WAdm_NativeInstall.install (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)).op16
          (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
          run.p {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
          f.proof f.pub () = ok saved ∧ Tx1Q_Endpoint.WhenBound run) ∧
      (let sdk := Op5T_SamePair.dictionary adapterOps (Uni_Install.base ops reserved queryOps geoOps) (Tx2N_Execution.control stageBase reserved queryOps geoOps) finishOps B claimsStd
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
      (Tx2N_Execution.control stageBase reserved queryOps geoOps).op18 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) s.checkpoint s.proof s.pub .S2 () = ok (.Ok (p,saved)) ∧
      (Tx2N_Execution.control stageBase reserved queryOps geoOps).op6 s.proof p saved g none geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      (Tx2N_Execution.control stageBase reserved queryOps geoOps).op9 after returned.weights.deref = ok flushed ∧
      let a := {returned with weights := back flushed}
      (Tx2I_Install.stage (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps).op19 v p a none = ok (.Ok ()) ∧
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
      ((RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved queryOps geoOps) B claimsStd).op3 f.proof = ok (.Ok .S2) ∧
        Op3I_Install.sourceBody f.proof = ok (.Ok .S2) ∧
        OraclePortHeader.accepts (bytesOf f.proof.val) = true ∧
        Op3I_Cuts.frozenHeader (bytesOf f.proof.val) = some .S2) ∧
      S2W_ExpandedTrace.runExpanded (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) (children port)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) e1.first (e2.second secondSizes) saved
          {f with semantic := selectedPublic} s ∧
        ∃ (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
          (sem : r1_semantic.Verified Unit) (claimsPrefix : AspisR1PublicPreparation.r1_wire.Prefix),
          AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1 = ok (.Ok v) ∧
          (semanticBase (Uni_Install.current ops reserved queryOps geoOps) (ClaimsUnrolledFinish.install claimsStd B)).op9
            (NativeBuffers.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (withValues (Uni_Install.current ops reserved queryOps geoOps)) nativeValues
              AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install claimsStd B))
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic
                (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
            v.semantic () none = ok (.Ok sem) ∧
          AspisR1PublicPreparation.PrefixAdapter.parseAccepted v.semantic = ok (.Ok claimsPrefix) ∧
          ClaimsUnrolledFinish.reference claimsStd claimsPrefix = ok (.Ok (retainedSem sem).claims)) ∧
      let decode := CPhy_Header.decode
      let nodes := CPhy_Ranges.nodes f.proof s.proof
      let y1 := CPhy_Ranges.y1 f.proof
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) ∧
        ∀ (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
          (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
          (domain : Port5Q1_Domain.SessionADomain geoOps)
          (multiply : geoOps.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
          (one : geoOps.op7 = ok 1#u32) (inverse : geoOps.op11 = Port4C_InverseExecution.inverse_owned),
        Tx2N_Finish.Outcome finishOps reserved queryOps
          (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
            (sdkOps (Tx2I_Install.install adapterOps
              (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps)
              (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) ()
          s.pub s.proof s.checkpoint saved H (bytesOf f.proof.val) (bytesOf f.pub.val) := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,scan,tx1,batches,tx2,first,expanded,owned,
    layout,unchanged,before1,before2,claims,caller⟩ :=
    CPhy_Accepted.accepted_pair_unified L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd native1 native2
      prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length
  have oracle := S2W_DigestExtraction.native_oracle _ native1 native2 hashv extraction sha256 H p1 syscall
  obtain ⟨run,r,sp,n,w,can,write,domain,wide,content,native,bound⟩ := tx1
  have written := CPhy_Header.writer _ () H oracle _ _ f.proof f.pub saved write
  have writer : CheckpointWriterConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) CPhy_Header.decode H f.semantic f.pub f.proof f.split := by
    constructor
    · intro checkpoint success
      have eq := core.result.Result.Ok.inj (Result.ok.inj (cuts.first.symm.trans success))
      simpa only [← eq] using written.1
    · intro checkpoint success
      have eq := core.result.Result.Ok.inj (Result.ok.inj (cuts.first.symm.trans success))
      simpa only [← eq] using written.2
  obtain ⟨p2,a2,g2,geo2,pending2,out2,after2,flushed2,back2,v2,read,tail⟩ := tx2.2.2.2
  have resumed := Port4A_ReaderInstall.accepted_source stageBase reserved _ () s.checkpoint s.proof s.pub .S2 p2 a2 read
  have checked := CPhy_Header.reader reserved _ () H oracle s.checkpoint s.proof s.pub p2 a2 resumed
  have reader : CheckpointReaderConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control stageBase reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) CPhy_Header.decode H s.pub s.proof s.checkpoint := ⟨fun _ => checked⟩
  have length0 : f.proof.val.length = 57607 := by
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using
      ((OraclePortHeader.accepts_iff _).mp first.2.2.1).1
  have length1 : s.proof.val.length = 57607 := by
    simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using
      ((OraclePortHeader.accepts_iff _).mp tx2.2.2.1).1
  have multiproof := CPhy_Ranges.multiproof f.proof s.proof length0 length1
  have scanned := CPhy_Ranges.scan f.proof length0 scan.2.1
  refine ⟨f,s,outer,pre,middle,fs,ss,cuts,writer,reader,multiproof,scanned.1,scanned.2,
    scan,⟨run,r,sp,n,w,can,write,domain,wide,content,native,bound⟩,batches,tx2,first,expanded,owned,
    layout,unchanged,before1,before2,claims,?_⟩
  dsimp only
  intro runtime p2prime entry
  exact caller CPhy_Header.decode (CPhy_Ranges.nodes f.proof s.proof) (CPhy_Ranges.y1 f.proof)
    writer reader runtime p2prime entry multiproof scanned.1

#print axioms accepted_pair_unified
#print accepted_pair_unified
end AspisR1.CPhy_Physical
end
