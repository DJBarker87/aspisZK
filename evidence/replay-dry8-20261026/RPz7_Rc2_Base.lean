import RPz7_Cons_Base
import RPz7_NP6_ParsedClaims
import RPz7_NP6_Constructors
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_Cons_Ten
import RPz7_Cons_Finish
import RPz7_Cons_Native
import RPz7_Cons_Continuation
import RPz7_T2Nat_ReaderEffects
import RPz7_CPhy_Physical
import T2Nat_FinishResult
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
namespace AspisR1.Rc2_Base
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

def Outcome {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) (outer : S2W_Trace.Log)
    (pre middle : List (S2W_SiteSchedule.Event (Option Unit)))
    (fs : S2W_SiteSchedule.FirstSegments (Option Unit))
    (ss : S2W_SiteSchedule.SecondSegments (Option Unit))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B (NP6_StdModel.calls reservation))
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B (NP6_StdModel.calls reservation)) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved) : Prop :=
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps B (NP6_StdModel.calls reservation);
      SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) e1.first (e2.second secondSizes) saved f s ∧
      CheckpointWriterConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) CPhy_Header.decode H f.semantic f.pub f.proof f.split ∧
      CheckpointReaderConeJoin (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) CPhy_Header.decode H s.pub s.proof s.checkpoint ∧
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof (CPhy_Ranges.nodes f.proof s.proof) ∧
      S2W_ChildJoins.S8StageConeJoin f.proof (CPhy_Ranges.y1 f.proof) ∧
      Op4P_Extract.Op4P_reference.reference.check_values (CPhy_Ranges.y1 f.proof) = ok true ∧
      ((RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)).op4 f.proof = ok (.Ok ()) ∧
        Op4P_Install.sourceBody f.proof = ok (.Ok ()) ∧
        OraclePortCompactDraft.scan (bytesOf f.proof.val)) ∧
      (reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
        (∀ x ∈ (Tx1Q_Carriers.slice Tx1Q_Carriers.k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
        Port3_CheckpointInstall.writer
          (Tx1Q_Install.digest (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B (NP6_StdModel.calls reservation)))
          (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
          f.proof f.pub () = ok saved ∧
        WAdm_Domain.Admitted (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ∧
        WAdm_Carrier.WideInputs (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) ∧
        WAdm_SourceWriter.writer (Tx1Q_Install.digest (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B (NP6_StdModel.calls reservation)))
          (Tx1Q_Carriers.prepared run.p)
          (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
          f.proof f.pub () = ok saved ∧
        (WAdm_NativeInstall.install (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B (NP6_StdModel.calls reservation))).op16
          (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B (NP6_StdModel.calls reservation))
          run.p {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
          f.proof f.pub () = ok saved) ∧
      (let sdk := Op5T_SamePair.dictionary adapterOps (Uni_Install.base ops reserved queryOps geoOps) (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps) finishOps B (NP6_StdModel.calls reservation)
       let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk
       let currentD := AspisS6CurrentFirstInstallation.toDigest D
       ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
         (p1 : VTop_Stages.verifier.Prepared) (root1 : Array U8 32#usize),
         Op5T_Install.currentBatch Port4B_Install.leaves currentD f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
         Op5T_Install.stageBatch Port4B_Install.leaves D s.proof p1 root1 1#usize () = ok (.Ok ())) ∧
      (Tx2I_Install.shape s.proof = ok (.Ok .S2) ∧
    Op3I_Install.sourceBody s.proof = ok (.Ok .S2) ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf s.proof.val) = true) ∧
      ((RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)).op3 f.proof = ok (.Ok .S2) ∧
        Op3I_Install.sourceBody f.proof = ok (.Ok .S2) ∧
        OraclePortHeader.accepts (bytesOf f.proof.val) = true ∧
        Op3I_Cuts.frozenHeader (bytesOf f.proof.val) = some .S2) ∧
      S2W_ExpandedTrace.runExpanded (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) (children port)
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation))
        (S2W_Observation.two (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B (NP6_StdModel.calls reservation)) e1.first (e2.second secondSizes) saved
          {f with semantic := selectedPublic} s ∧
        ∃ (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
          (sem : r1_semantic.Verified Unit) (claimsPrefix : AspisR1PublicPreparation.r1_wire.Prefix),
          AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1 = ok (.Ok v) ∧
          (semanticBase (Uni_Install.current ops reserved queryOps geoOps) (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) B)).op9
            (NativeBuffers.callerDigest (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (withValues (Uni_Install.current ops reserved queryOps geoOps)) nativeValues
              AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) B))
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic
                (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
            v.semantic () none = ok (.Ok sem) ∧
          AspisR1PublicPreparation.PrefixAdapter.parseAccepted v.semantic = ok (.Ok claimsPrefix) ∧
          ClaimsUnrolledFinish.reference (NP6_StdModel.calls reservation) claimsPrefix = ok (.Ok (retainedSem sem).claims) ∧
          NP6_ClaimsRun.Content reservation claimsPrefix (retainedSem sem).claims ∧
          NP6_ParsedClaims.Content reservation v.semantic claimsPrefix (retainedSem sem).claims)
theorem strengthen {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) (outer : S2W_Trace.Log)
    (pre middle : List (S2W_SiteSchedule.Event (Option Unit)))
    (fs : S2W_SiteSchedule.FirstSegments (Option Unit))
    (ss : S2W_SiteSchedule.SecondSegments (Option Unit))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B (NP6_StdModel.calls reservation))
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B (NP6_StdModel.calls reservation)) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (base : Cons_Base.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps
      stageBase finishOps B (NP6_StdModel.calls reservation) program data1 data2 slot
      saved post1 post2 H f s outer pre middle fs ss run) :
    Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B
      reservation program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run := by
  obtain ⟨cuts,writer,reader,multiproof,scanY,checkY,scan,tx1,batches,header2,header1,
    expanded,owned,projectedRun,heap2,obs1,obs2,claims⟩ := base
  refine ⟨cuts,writer,reader,multiproof,scanY,checkY,scan,tx1,batches,header2,header1,
    expanded,owned,projectedRun,heap2,obs1,obs2,?_⟩
  obtain ⟨selected,selectedCall,selectedCuts,semantic,y1,v,sem,claimsPrefix,
    wide,semanticCall,parsed,normalized⟩ := claims
  exact ⟨selected,selectedCall,selectedCuts,semantic,y1,v,sem,claimsPrefix,
    wide,semanticCall,parsed,normalized,
    NP6_ClaimsRun.on_success reservation claimsPrefix _ normalized,
    NP6_ParsedClaims.on_success reservation v.semantic claimsPrefix _ parsed normalized⟩

#print axioms strengthen
end AspisR1.Rc2_Base
end
