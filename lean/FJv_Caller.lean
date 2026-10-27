import FIs_Caller
import FJv_Cont
import P2P_Caller
import FIs_Cont
import PFin_Attach
import Rc5_Caller
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import T2R_Ten
import T2R_Finish
import Cons_Native
import T2R_ContSource
import T2Nat_ReaderEffects
import CPhy_Physical
import T2Nat_FinishResult
import SAF_C_SAF_PreparedCaller
import Rc5_Cont
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
namespace AspisR1.FJv_Caller
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
        FJv_Cont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps
          B claimsStd prior H f s saved run tx2
theorem strengthen {W C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation)
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) (outer : S2W_Trace.Log)
    (pre middle : List (S2W_SiteSchedule.Event (Option Unit)))
    (fs : S2W_SiteSchedule.FirstSegments (Option Unit))
    (ss : S2W_SiteSchedule.SecondSegments (Option Unit))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current (FIp_Install.configuration err seed r).currentBase) (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) claimsStd)
      (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry (SdkD_PairBatches.current (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (prior : Program Bytes State Unit) (tx2 : Cons_Native.Witness)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install (FIp_Install.configuration err seed r).adapter
          (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (FIp_Install.configuration err seed r).stageBase)
            (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
            (FIp_Install.configuration err seed r).geometry)) (FIp_Install.configuration err seed r).finish)
        (Uni_Install.current (FIp_Install.configuration err seed r).currentBase
          (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
          (FIp_Install.configuration err seed r).geometry) (F3M_CircleSource.install B) claimsStd)
      e1.first (e2.second secondSizes) saved f s)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (⟨(FIp_Install.configuration err seed r).adapter,(FIp_Install.configuration err seed r).currentBase,
        (FIp_Install.configuration err seed r).stageBase,(FIp_Install.configuration err seed r).finish,
        (FIp_Install.configuration err seed r).reserved,(FIp_Install.configuration err seed r).query,
        (FIp_Install.configuration err seed r).geometry,F3M_CircleSource.install B,claimsStd⟩ : DrvC_Installation.Configuration FIo_Install.W C))
      native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (rootBinding : FJp_RootBinding.Holds f.proof run.root)
    (enriched : FIs_Native.Calls (AuS1_Install.base (FIp_Install.configuration err seed r).stageBase)
      (FIp_Install.configuration err seed r).finish (FIp_Install.configuration err seed r).reserved
      (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry
      (Tx1Q_Install.digest (SdkD_PairBatches.current
        (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase
        (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish
        (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query
        (FIp_Install.configuration err seed r).geometry (F3M_CircleSource.install B) claimsStd)) () s.pub s.proof s.checkpoint tx2)
    (old : FIs_Caller.Outcome L e1 e2 w1 w2 (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2) :
    Outcome L e1 e2 w1 w2 (FIp_Install.configuration err seed r).adapter (FIp_Install.configuration err seed r).currentBase (FIp_Install.configuration err seed r).reserved (FIp_Install.configuration err seed r).query (FIp_Install.configuration err seed r).geometry (FIp_Install.configuration err seed r).stageBase (FIp_Install.configuration err seed r).finish B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2 := by
  let c := FIp_Install.configuration err seed r
  obtain ⟨parsed,facts,sites,cont⟩ := old
  have reachedTx2 := S2W_SiteSchedule.reached pre middle fs ss .tx2
  have sameProof : bytesOf s.proof.val=bytesOf f.proof.val := by
    simpa only [S2W_InputSchedule.observation,show ¬ S2LeadInterface.Site.tx2.rank ≤ 3 by decide,if_false] using facts.proofBytes .tx2 reachedTx2
  have sameSaved : bytesOf s.checkpoint.val=bytesOf saved.val := by
    simpa only [S2W_InputSchedule.observation,show ¬ S2LeadInterface.Site.tx2 = .save by decide,if_false] using facts.checkpointBytes .tx2 reachedTx2 (Or.inr (Or.inl rfl))
  have size : f.proof.val.length=57607 := by
    simpa only [bytesOf,List.length_map] using facts.proofLength
  refine ⟨parsed,facts,sites,?_⟩
  exact FJv_Cont.strengthen err seed r B claimsStd saved f s run prior H tx2 e1.first
    (e2.second secondSizes) cuts native1 native2 hashv extraction sha256 p1 syscall sameProof sameSaved size rootBinding enriched cont
#print axioms strengthen
end AspisR1.FJv_Caller
end
