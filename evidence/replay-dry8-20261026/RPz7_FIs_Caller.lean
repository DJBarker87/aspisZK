import RPz7_P2P_Caller
import RPz7_FIs_Cont
import RPz7_PFin_Attach
import RPz7_Rc5_Caller
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_T2R_Ten
import RPz7_T2R_Finish
import RPz7_Cons_Native
import RPz7_T2R_ContSource
import RPz7_T2Nat_ReaderEffects
import RPz7_CPhy_Physical
import T2Nat_FinishResult
import RPz7_SAF_C_SAF_PreparedCaller
import RPz7_Rc5_Cont
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
namespace AspisR1.FIs_Caller
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
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) (outer : S2W_Trace.Log)
    (pre middle : List (S2W_SiteSchedule.Event (Option Unit)))
    (fs : S2W_SiteSchedule.FirstSegments (Option Unit))
    (ss : S2W_SiteSchedule.SecondSegments (Option Unit))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (prior : Program Bytes State Unit) (tx2 : Cons_Native.Witness) : Prop :=
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps (F3M_CircleSource.install B) claimsStd
      let decode := CPhy_Header.decode
      let nodes := CPhy_Ranges.nodes f.proof s.proof
      let y1 := CPhy_Ranges.y1 f.proof
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) ∧
        FIs_Cont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps
          B claimsStd prior H f s saved run tx2
theorem strengthen {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) (outer : S2W_Trace.Log)
    (pre middle : List (S2W_SiteSchedule.Event (Option Unit)))
    (fs : S2W_SiteSchedule.FirstSegments (Option Unit))
    (ss : S2W_SiteSchedule.SecondSegments (Option Unit))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (prior : Program Bytes State Unit) (tx2 : Cons_Native.Witness)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (enriched : FIs_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps D hash s.pub s.proof s.checkpoint tx2)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F) (installed : finishOps=FIn_Install.finishOps seed)
    (positions : stageBase.op22=ok 7527#usize ∧ stageBase.op21=ok 8007#usize ∧ stageBase.op20=ok 10055#usize)
    (old : P2P_Caller.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2) :
    Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2 := by
  obtain ⟨parsed,facts,sites,cont⟩ := old
  have reachedTx2 := S2W_SiteSchedule.reached pre middle fs ss .tx2
  have sameProof : bytesOf s.proof.val=bytesOf f.proof.val := by
    simpa only [S2W_InputSchedule.observation,show ¬ S2LeadInterface.Site.tx2.rank ≤ 3 by decide,if_false] using facts.proofBytes .tx2 reachedTx2
  have sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val := by
    simpa only [S2W_InputSchedule.observation,show ¬ S2LeadInterface.Site.tx2 = .save by decide,if_false] using facts.checkpointBytes .tx2 reachedTx2 (Or.inr (Or.inl rfl))
  exact ⟨parsed,facts,sites,FIs_Cont.strengthen adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd
    prior H f s saved run tx2 D hash enriched seed installed positions sameProof sameSaved cont⟩

#print axioms strengthen
end AspisR1.FIs_Caller
end
