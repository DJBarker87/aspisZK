import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import Cons_Ten
import Cons_Finish
import Cons_Native
import T2Nat_ReaderEffects
import CPhy_Physical
import T2Nat_FinishResult
import CPhy_Header
import CPhy_Ranges
import CPhy_Accepted
import WAdm_NativeEndpoint
import SdkD_Accepted
import SdkD_Inner
import SdkD_Uni
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Cons_Pair
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
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
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
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
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
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps B claimsStd
    ∃ f s outer pre middle fs ss,
      ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
        reserved queryOps geoOps (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd) ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ tx2 : Cons_Native.Witness,
      Cons_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) () s.pub s.proof s.checkpoint tx2 ∧
      SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) e1.first (e2.second secondSizes) saved f s ∧
      CheckpointWriterConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) CPhy_Header.decode H f.semantic f.pub f.proof f.split ∧
      CheckpointReaderConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) CPhy_Header.decode H s.pub s.proof s.checkpoint ∧
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof (CPhy_Ranges.nodes f.proof s.proof) ∧
      S2W_ChildJoins.S8StageConeJoin f.proof (CPhy_Ranges.y1 f.proof) ∧
      Op4P_Extract.Op4P_reference.reference.check_values (CPhy_Ranges.y1 f.proof) = ok true ∧
      ((RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved queryOps geoOps) B claimsStd).op4 f.proof = ok (.Ok ()) ∧
        Op4P_Install.sourceBody f.proof = ok (.Ok ()) ∧
        OraclePortCompactDraft.scan (bytesOf f.proof.val)) ∧
      (reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
        (∀ x ∈ (Tx1Q_Carriers.slice Tx1Q_Carriers.k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
        Port3_CheckpointInstall.writer
          (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd))
          (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
          f.proof f.pub () = ok saved ∧
        WAdm_Domain.Admitted (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ∧
        WAdm_Carrier.WideInputs (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) ∧
        WAdm_SourceWriter.writer (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd))
          (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
          f.proof f.pub () = ok saved ∧
        (WAdm_NativeInstall.install (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)).op16
          (Tx1Q_SameCut.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd)
          run.p {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
          f.proof f.pub () = ok saved) ∧
      (let sdk := Op5T_SamePair.dictionary adapterOps (Uni_Install.base ops reserved queryOps geoOps) (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps) finishOps B claimsStd
       let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk
       let currentD := AspisS6CurrentFirstInstallation.toDigest D
       ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
         (p1 : VTop_Stages.verifier.Prepared) (root1 : Array U8 32#usize),
         Op5T_Install.currentBatch Port4B_Install.leaves currentD f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
         Op5T_Install.stageBatch Port4B_Install.leaves D s.proof p1 root1 1#usize () = ok (.Ok ())) ∧
      (Tx2I_Install.shape s.proof = ok (.Ok .S2) ∧
    Op3I_Install.sourceBody s.proof = ok (.Ok .S2) ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf s.proof.val) = true) ∧
      ((RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved queryOps geoOps) B claimsStd).op3 f.proof = ok (.Ok .S2) ∧
        Op3I_Install.sourceBody f.proof = ok (.Ok .S2) ∧
        OraclePortHeader.accepts (bytesOf f.proof.val) = true ∧
        Op3I_Cuts.frozenHeader (bytesOf f.proof.val) = some .S2) ∧
      S2W_ExpandedTrace.runExpanded (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) (children port)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) e1.first (e2.second secondSizes) saved
          {f with semantic := selectedPublic} s ∧
        ∃ (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
          (sem : r1_semantic.Verified Unit) (claimsPrefix : AspisR1PublicPreparation.r1_wire.Prefix),
          AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1 = ok (.Ok v) ∧
          (semanticBase (Uni_Install.current ops reserved queryOps geoOps) (ClaimsUnrolledFinish.install claimsStd B)).op9
            (NativeBuffers.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (withValues (Uni_Install.current ops reserved queryOps geoOps)) nativeValues
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
          (S2Z.Oracle.leadDigest (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) ∧
        ∀ (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
          (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
          (domain : Port5Q1_Domain.SessionADomain geoOps)
          (multiply : geoOps.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
          (one : geoOps.op7 = ok 1#u32) (inverse : geoOps.op11 = Port4C_InverseExecution.inverse_owned),
        ∃ authParsed frame,
          OraclePortCompactDraft.parse (bytesOf f.proof.val) = some authParsed ∧
          FS2.Duplex.Read ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
            (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) frame ∧
          BinRawByteCollisionTargets.pred 3 frame = some (OraclePortBatchDraft.committedRoot authParsed 2) ∧
          Cons_Ten.Outcome run H ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) authParsed ∧
          Cons_Finish.Outcome finishOps tx2.v2 tx2.p2 {tx2.returned2 with weights := tx2.back2 tx2.flushed2}
            s.proof saved H (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed
            ((eval H prior).1 ++ AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) B claimsStd
              (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
              (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)) := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,writer,reader,multiproof,scanY,checkY,
    scan,oldTx1,batches,tx2,first,expanded,owned,layout,unchanged,before1,before2,claims,caller⟩ :=
    T2Nat_NativePair.accepted_pair_unified L sdk copy std allocator e1 e2 w1 w2
      admission1 admission2 adapterOps ops reserved queryOps geoOps (AuS1_Install.base stageBase) finishOps
      B claimsStd native1 native2 prepareOwner primitiveOwner hashv extraction
      sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 p root length
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
      e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact cuts
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
      native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  obtain ⟨run,rootView,rootRange,rootCopy⟩ := SdkD_PairBatches.first_run adapterOps ops stageBase finishOps
    reserved queryOps geoOps B claimsStd e1.first (e2.second secondSizes) saved f s pairCuts
  have control := Tx1Q_Control.fields _ _ _ _ _ _ _ _ _ _ _ run
  have proofLength : f.proof.val.length = 57607 := by
    simpa only [bytesOf,List.length_map] using cuts.proofLength
  have publicLength := (WAdm_Public.reached _ _ B claimsStd e1 _ saved f s cuts).2
  have domain := WAdm_Domain.on_run _ _ _ _ _ _ _ _ _ _ _ run prepareOwner primitiveOwner proofLength publicLength
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run _ _ _ _ _ _ _ _ _ _ _ run prepareOwner primitiveOwner
  have nativeContent := WAdm_NativeInstall.on_run _ _ _ _ _ _ _ _ _ _ _ run prepareOwner primitiveOwner
  have sourceContent : WAdm_SourceWriter.writer
      (Tx1Q_Install.digest (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd))
      (Tx1Q_Carriers.prepared run.p)
      (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub () = ok saved := by
    rw [WAdm_SourceWriter.writer_eq _ _ _ _ _ _ fields size canonical control.2.2.1]
    exact run.writer_call
  have authenticated : VTop_Stages.verifier.candidate.tx2_authenticated
      (Tx2I_Install.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps) finishOps)
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (sdkOps (Tx2I_Install.install adapterOps
          (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps)
          (Uni_Install.current ops reserved queryOps geoOps) B claimsStd))
      s.pub s.proof s.checkpoint () none = ok (.Ok ()) := cuts.second
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ _ () s.pub s.proof s.checkpoint none authenticated
  have commonRun : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control (Tx2I_Install.stage (AuS1_Install.base stageBase) finishOps) reserved queryOps geoOps)
      _ s.pub s.proof s.checkpoint () none = ok (.Ok ()) := common
  obtain ⟨p2,saved2,g2,geometry2,pending2,returned2,after2,flushed2,back2,v2,
    hr,hnext,hg,hgeo,hpending,hquery,hback,hflush,hfinish⟩ :=
    Tx2N_Execution.common (Tx2I_Install.stage (AuS1_Install.base stageBase) finishOps)
      reserved queryOps geoOps _ () s.pub s.proof s.checkpoint commonRun
  have native := T2Nat_ReaderJoin.on_run (AuS1_Install.base stageBase) reserved queryOps _ ()
    s.checkpoint s.proof s.pub p2 saved2 hr
  have logs := T2Nat_ReaderEffects.on_run (AuS1_Install.base stageBase) reserved queryOps _ ()
    s.checkpoint s.proof s.pub p2 saved2 hr
  have finishCall : Port4D_FinishInstall.finish finishOps v2 p2
      {returned2 with weights := back2 flushed2} none = ok (.Ok ()) := hfinish
  let tx2run : Cons_Native.Witness := ⟨p2,saved2,g2,geometry2,pending2,returned2,after2,flushed2,back2,v2⟩
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2run,?_,cuts,writer,reader,multiproof,scanY,checkY,scan,?_,batches,?_,first,expanded,owned,layout,
    unchanged,before1,before2,claims,?_⟩
  · refine ⟨hr,native.1,native.2.1,native.2.2,logs,hquery,hback,hflush,hfinish,finishCall,?_⟩
    intro Hash D hash before
    exact T2Nat_FinishResult.accepted_effects D hash finishOps v2 p2
      {returned2 with weights := back2 flushed2} finishCall before
  · exact ⟨control.1,control.2.1,control.2.2.1,control.2.2.2.1,control.2.2.2.2,
      run.writer_call,domain,WAdm_Carrier.wide _ _ _ _ domain,sourceContent,nativeContent⟩
  · exact ⟨tx2.1,tx2.2.1,tx2.2.2.1⟩
  · dsimp only
    intro runtime p2prime entry
    obtain ⟨parsed,facts,sites,oldOutcome⟩ := caller runtime p2prime entry
    obtain ⟨version,key,ledger,events,sameCheckpoint,sameProof,samePub,savedLength⟩ :=
      RowOrder_History.on_d189_cuts copy std allocator e1 e2 _ native1 native2 hashv extraction
        program data1 state1 final1 saved post1 accepted1 f s cuts CPhy_Header.decode H writer reader runtime p2prime
    obtain ⟨tr,authParsed,parseReached⟩ := entry.parsed
    have parser := (OraclePortStoredParserC4.parsed _ _ _ parseReached).1
    obtain ⟨frame,frameRead,target,auth⟩ := AuS1_OnRun.same_pair prior adapterOps ops stageBase finishOps
      reserved queryOps geoOps B claimsStd native1 native2 hashv pairExtraction sha256 H p1 syscall
      e1.first (e2.second secondSizes) saved f s pairCuts sameCheckpoint sameProof authParsed parser
      run rootView rootRange rootCopy
    refine ⟨parsed,facts,sites,?_⟩
    intro queryLeaves geoLeaves domain multiply one inverse
    have old := oldOutcome queryLeaves geoLeaves domain multiply one inverse
    refine ⟨authParsed,frame,parser,frameRead,target,?_,?_⟩
    · intro ports q tr data rho prepare parseReached read geo domain multiply one inverse
      rcases auth data rho q prepare with collision | indexed
      · exact Or.inl collision
      · exact Or.inr (Tx1Q_Endpoint.on_run _ _ _ _ _ _ _ _ _ _ _ run proofLength
          ports authParsed q tr data rho prepare parseReached read
          (OraclePortAllSelectedRecoveryC6.recovered _ frame authParsed 2) indexed
          geo domain multiply one inverse)
    · intro alpha0 alpha1 r0 r1 weights alphas pair dot s2 ha0 ha1 hw has hp hd
        semantic q tr i hi hq read decoded pairing matchesLaw equation dotLaw canonical c prepare tx1_saved
      rcases auth i.data (SelectedChallengeMap.rhoOf i.rho) q prepare with collision | indexed
      · exact Or.inl collision
      · right
        have wire := (OraclePortCompactDraft.parse_header _ _ parser).2.trans sameProof.symm
        have indexed' : ∀ pos, pos < 22 →
            OraclePortAllSelectedRecoveryC6.recovered _ frame authParsed 2
              (OraclePortSelectedDraft.index q 2 pos) =
                some (OraclePortPackedChoiceC4.payload ⟨bytesOf s.proof.val,semantic⟩ 2 pos) := by
          intro pos bound
          simpa only [OraclePortPackedChoiceC4.payload,OraclePortSelectedDraft.opening,wire] using indexed pos bound
        have fields := Tx2N_Reader.saved_ten (AuS1_Install.base stageBase) reserved queryOps _ ()
          s.checkpoint s.proof s.pub saved p2 saved2 H (bytesOf f.proof.val) (bytesOf f.pub.val)
          c i.data (SelectedChallengeMap.rhoOf i.rho) q sameCheckpoint tx1_saved hr
        have hgeo' := hgeo
        rw [hnext] at hgeo'
        have geometry := Port5Q1_GeometryReads.accepted geoOps geoLeaves domain multiply one inverse
          p2.queries 10#usize 22#usize geometry2 (by decide) hgeo'
        have proofLength2 : s.proof.val.length = 57607 := by
          have lengths := congrArg List.length sameProof
          simpa only [bytesOf,List.length_map,proofLength] using lengths
        have twelve := Tx2N_Query.twelve queryOps queryLeaves s.proof p2 saved2 returned2 g2 geometry2
          pending2 after2 flushed2 back2 ⟨bytesOf s.proof.val,semantic⟩ q tr i.data
          (SelectedChallengeMap.rhoOf i.rho) c _ fields.1 hnext read rfl proofLength2
          (OraclePortAllSelectedRecoveryC6.recovered _ frame authParsed 2) indexed' geometry reserved
          hpending hquery hback hflush
        have values := FinT_Model.finish_value finishOps v2 p2 _ saved2 alpha0 alpha1 r0 r1 weights alphas pair dot
          s2 ha0 ha1 hw has hp hd ⟨bytesOf s.proof.val,semantic⟩ q tr i hi hq read decoded pairing
          matchesLaw equation dotLaw canonical fields.2.1 twelve
        refine ⟨values.1,values.2,?_⟩
        rw [← values.2]
        simp only [finishCall,decide_true]

#print axioms accepted
end AspisR1.Cons_Pair
end
