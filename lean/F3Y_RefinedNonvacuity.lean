import F3Y_RefinedHeadline
import F3X_FixtureRuntime
import F3X_FixtureSource
import F3X_FixtureHistory
import F3X_FixtureBinding
import F3X_ModelClaims
import F3X_Native
import F3Y_Bound
import F3X_Installation
import F3U_Range
import Rc2_Install
import Rc2_Result
import Rc2_Events
import Rc2_Protection
import PoolT_Write
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
namespace AspisR1.F3Y_RefinedNonvacuity
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
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

theorem composed {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (F3X_Installation.configuration c reservation).currentBase) (F3X_Installation.configuration c reservation).reserved (F3X_Installation.configuration c reservation).query (F3X_Installation.configuration c reservation).geometry (F3X_Installation.configuration c reservation).boundaries (F3X_Installation.configuration c reservation).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (F3X_Installation.configuration c reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (F3X_Installation.configuration c reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (F3X_Installation.configuration c reservation).stageBase) (F3X_Installation.configuration c reservation).reserved (F3X_Installation.configuration c reservation).query (F3X_Installation.configuration c reservation).geometry)) (F3X_Installation.configuration c reservation).finish) (Uni_Install.current (F3X_Installation.configuration c reservation).currentBase (F3X_Installation.configuration c reservation).reserved (F3X_Installation.configuration c reservation).query (F3X_Installation.configuration c reservation).geometry) (F3X_Installation.configuration c reservation).boundaries (F3X_Installation.configuration c reservation).std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (D : LiteralByteProtocol.Decoder) (submission : F3T_ByteCarrier.Submission)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives (F3X_Installation.configuration c reservation).geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain (F3X_Installation.configuration c reservation).geometry)
    (multiply : (F3X_Installation.configuration c reservation).geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : (F3X_Installation.configuration c reservation).geometry.op7=ok (1#u32))
    (inverse : (F3X_Installation.configuration c reservation).geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : F3Y_PreparedAt.Owners (F3X_Installation.configuration c reservation)
      (Rc2_Install.configuration c reservation).boundaries)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (keyLaw : (DrvC_Installation.sdk (F3X_Installation.configuration c reservation)).op36=Hist_Authority.keyEq)
    (initial : CPP_BankState.Bank) (layout : Hist_RuntimeEntry.Layout)
    (entry1 : e1=Hist_RuntimeEntry.load initial.cells (CPP_BankState.layout initial layout))
    (actions : List (CPP_BankState.Action A)) (positive : 0 < initial.lamports (layout.handles 2).1)
    (entry2 : F3X_GameFixture.loaded
      (CPP_BankHistory.run native1 native2 copy allocator program
        (CPR_SourceBank.afterCopy initial (layout.handles 2).1 saved) actions).1 true (layout.handles 2).1=
      some (bytesOf (e2.buffers (e2.handles 6).1).val))
    (snapshots : ∀ f s,SourceCuts (DrvC_Installation.sdk (F3X_Installation.configuration c reservation))
      e1.first (e2.second secondSizes) saved f s →
      bytesOf s.proof.val=bytesOf f.proof.val ∧ bytesOf s.pub.val=bytesOf f.pub.val ∧
      bytesOf f.pub.val=submission.publicBytes ∧ bytesOf f.proof.val=submission.stored) :
    let r := F3X_Installation.configuration c reservation
    let runtime := F3X_FixtureRuntime.runtime r D hashv (.done submission)
    F3T_Runtime.StoredCarrierBinding r D (F3T_Installed.source r hashv) (.done submission) runtime ∧
    (eval H (F3T_Installed.source r hashv (F3T_ByteCarrier.input r submission))).2=true ∧
    (∃ run,(eval H runtime).2=some run ∧ run.2.2=true) ∧
    F3T_RuntimeBound.failureModel runtime<1/(2:Rat)^100 ∧
    ∃ (f : FirstCut) (s : SecondCut),SourceCuts (DrvC_Installation.sdk r)
      e1.first (e2.second secondSizes) saved f s ∧
      ∃ version : S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val),
        version.events=(eval H (CPS_BankRecorder.program r hashv native1 native2 copy allocator program
          (CPR_SourceBank.afterCopy initial (layout.handles 2).1 saved) actions)).2.2 ∧
        S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub := by
  dsimp only
  let r := F3X_Installation.configuration c reservation
  let runtime := F3X_FixtureRuntime.runtime r D hashv (.done submission)
  have binding := F3X_FixtureRuntime.binding r D hashv (.done submission)
  obtain ⟨driverEq,sdkEq,security,result,copyFacts,eventFacts,protectionFacts⟩ := F3Y_RefinedHeadline.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c reservation native1 native2
    prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior D
    (.done submission) 0 0 (fun _=>Nat.le_refl 0) runtime w canonicalOwner domainOwner multiply one inverse
    finishOwners binding select
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,contents,history,publicFacts,parser,acceptance,caller⟩ := result
  have cuts := base.1
  obtain ⟨sameProof,samePublic,pubBytes,proofBytes⟩ := snapshots f s cuts
  obtain ⟨version,events,persisted⟩ := F3X_FixtureHistory.binding r hashv native1 native2 copy allocator program
    e1 e2 saved post1 H f s history keyLaw initial layout entry1 actions positive entry2
  have checkpoint : bytesOf s.checkpoint.val=bytesOf saved.val := persisted.trans copyFacts.2.2.1
  have sourceAccepted := F3X_FixtureSource.accepted r native1 native2 hashv extraction sha256 H p1 syscall
    program e1.first (e2.second secondSizes) data1 saved copyFacts.1 f s cuts sameProof samePublic checkpoint
  have sameSubmission : (⟨bytesOf f.pub.val,bytesOf f.proof.val⟩ : F3T_ByteCarrier.Submission)=submission := by
    cases submission
    exact congrArg₂ Port1_StoredCarrier.Submission.mk pubBytes proofBytes
  rw [sameSubmission] at sourceAccepted
  refine ⟨binding,sourceAccepted,F3X_FixtureRuntime.accepted r D hashv submission H sourceAccepted,
    (security.2.2.2.2.2 rfl).2,f,s,cuts,version,events,?_⟩
  exact F3X_FixtureBinding.proof_public H f.proof f.pub s.proof s.pub sameProof samePublic

#print axioms composed
end AspisR1.F3Y_RefinedNonvacuity
end
