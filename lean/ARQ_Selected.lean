import Rc9_Top
import ARP_Interface
import FIp_Top
import S6N_Installation
import Rc8_Top
import Rc9_Install
import FIp_Install
import FIp_Core
import FIo_Nonvacuity
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.ARQ_Selected
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open FS FS2
open AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin
open RawExtractorCostComposedV2
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
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

/-- Exact Rc9 specialization on the response-selected entries in this H.
Every native/game/persistence/owner/binding premise is retained; no all-world
bank factory is inferred from this pointwise application. -/
theorem deployed {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (a : SCE_Experiment.Adversary A) (w1 w2 : W)
    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (admission1 : RuntimeEntrypointAdmission L (eval H a.first).2.entry w1 3)
    (admission2 : RuntimeEntrypointAdmission L
      (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry w2 7)
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator ((eval H a.first).2.entry) CPH_Program.verifier ((eval H a.first).2.data) ((eval H a.first).2.state) =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) CPH_Program.verifier ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.state) =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State, (eval H (SCE_Experiment.submission a)).1.length ≤ Q0+Q1)
    (finishOwners : FIp_GlobalOwners.Owners
      (FIp_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)
    (binding : F3T_Runtime.StoredCarrierBinding
      (FIp_Install.configuration indexError c reservation) D
      (F3T_Installed.source (FIp_Install.configuration indexError c reservation) hashv) (SCE_Experiment.submission a) (SCE_Experiment.runtime (FIp_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a))
    :
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot);
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase (FIp_Install.configuration indexError c reservation).stageBase
        (FIp_Install.configuration indexError c reservation).finish (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query (FIp_Install.configuration indexError c reservation).geometry
        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std ∧
    (P2P_Result.Outcome L ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) w1 w2
      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase
      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query
      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase
      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)
      reservation CPH_Program.verifier ((eval H a.first).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot) saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError c reservation) hashv (SCE_Experiment.submission a))
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D (SCE_Experiment.submission a) (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv (SCE_Experiment.submission a) (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv (SCE_Experiment.submission a) (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (FIp_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a) ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (FIp_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a) ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (FIp_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a) ∧
        F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (FIp_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a) < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier ((eval H a.first).2.entry).first ((eval H a.first).2.data) = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (((eval H a.first).2.entry).heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = ((eval H a.first).2.entry).heap.ambient ∧ post1.accounts = ((eval H a.first).2.entry).heap.accounts ∧
      post1.counter = ((eval H a.first).2.entry).heap.counter ∧
      (∀ cell, cell ≠ (((eval H a.first).2.entry).heap.accounts 2).1 → post1.payload cell = ((eval H a.first).2.entry).heap.payload cell)) ∧
    Rc2_Events.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) := by
  exact Rc9_Top.deployed L sdk copy std allocator ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) w1 w2 admission1 admission2 c indexError
    reservation native1 native2 hashv extraction sha256 H p1 syscall ((eval H a.first).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot)
    ((eval H a.first).2.state) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.state) final1 final2 saved post1 post2 accepted1 accepted2 root length prior words
    p t u actions game RuntimePersistence D (SCE_Experiment.submission a) Q0 Q1 queries
    (SCE_Experiment.runtime (FIp_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a)
    finishOwners binding

#print axioms deployed
#check @Rc9_Top.deployed
end AspisR1.ARQ_Selected
end
