import F3Y_Headline
import F3X_FixtureRuntime
import F3X_FixtureSource
import F3Y_InstalledLaws
import F3Y_Bound
import F3Y_SourceClaims
import F3Y_AccountMass
import F3X_ModelClaims
import F3U_Range
import Rc5_Source
import Rc5_Close
import Rc5_Install
import CPH_Recorder
import CPH_Trace
import CPH_Program
import CPH_Pair
import CPH_Protection
import Rc2_Events
import CPG_Pair
import CPG_Account
import CPP_Install
import F3T_ConditionalClaims
import CPG_History
import CPR_PhysicalResult
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import Cons_Pair
import Cons_Finish
import Cons_Native
import Cons_Continuation
import Cons_Base
import Cons_Caller
import Cons_Result
import T2R_FullResult
import T2R_Pair
import Par_Headline
import Par_Transcript
import Cons_NativeBuild
import Cons_FinishProof
import Cons_Second
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
namespace AspisR1.F3Y_Nonvacuity
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

theorem composed {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (submission : F3T_ByteCarrier.Submission)
    (finishOwners : F3Y_PreparedAt.Owners
      (Rc5_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation).boundaries)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (snapshots : ∀ f s,SourceCuts
      (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation))
      e1.first (e2.second secondSizes) saved f s →
      bytesOf s.proof.val=bytesOf f.proof.val ∧ bytesOf s.pub.val=bytesOf f.pub.val ∧
      bytesOf f.pub.val=submission.publicBytes ∧ bytesOf f.proof.val=submission.stored) :
    let r := Rc5_Install.configuration indexError c reservation
    let runtime := F3X_FixtureRuntime.runtime r D hashv (.done submission)
    F3T_Runtime.StoredCarrierBinding r D (F3T_Installed.source r hashv) (.done submission) runtime ∧
    (eval H (F3T_Installed.source r hashv (F3T_ByteCarrier.input r submission))).2=true ∧
    (∃ run,(eval H runtime).2=some run ∧ run.2.2=true) ∧
    F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
    F3T_RuntimeBound.failureModel runtime<1/(2:Rat)^100 := by
  dsimp only
  let r := Rc5_Install.configuration indexError c reservation
  let runtime := F3X_FixtureRuntime.runtime r D hashv (.done submission)
  have binding := F3X_FixtureRuntime.binding r D hashv (.done submission)
  obtain ⟨driverEq,sdkEq,result,security,copyFacts,eventFacts,protection,trace,recorder⟩ :=
    F3Y_Headline.deployed L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError
      reservation native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior words
      p t u actions game RuntimePersistence D (.done submission) 0 0 (fun _=>Nat.le_refl 0)
      runtime finishOwners binding select
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,encoding,base,contents,semantic,physical,parser,
    version,key1,key2,events,persisted,acceptance,nonvacuity,caller⟩ := result
  have cuts := base.1
  obtain ⟨sameProof,samePublic,pubBytes,proofBytes⟩ := snapshots f s cuts
  have checkpoint : bytesOf s.checkpoint.val=bytesOf saved.val := persisted.trans copyFacts.2.2.1
  have accepted := F3X_FixtureSource.accepted r native1 native2 hashv extraction sha256 H p1 syscall
    CPH_Program.verifier e1.first (e2.second secondSizes) data1 saved copyFacts.1 f s cuts
    sameProof samePublic checkpoint
  have same : (⟨bytesOf f.pub.val,bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission)=submission := by
    cases submission
    exact congrArg₂ Port1_StoredCarrier.Submission.mk pubBytes proofBytes
  rw [same] at accepted
  exact ⟨binding,accepted,F3X_FixtureRuntime.accepted r D hashv submission H accepted,
    security.2.2.2.2.2 rfl⟩

#print axioms composed
end AspisR1.F3Y_Nonvacuity
end
