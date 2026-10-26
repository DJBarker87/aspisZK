import SCE_Experiment
import Rc7_Native
import P2P_Release
import P2P_Accounting
import FGl_Cost
import Rc6_Result
import P6C_Extension
import F3Y_InstalledLaws
import FGl_Bound
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
namespace AspisR1.SCG_NativeAccount
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

open SCE_Experiment
/-- Retained native/game laws charged on the actual adaptive account recorder.
This derives the existing native acceptance-or-collision alternative at the
supplied H. It does not universalize admissions/game over other worlds. -/
theorem accepted {W A F CoreError Tx : Type}
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
    (a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    P2P_Result.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (SCE_Experiment.account (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a)
          project (fun _ => P2P_NativeSelection.pair (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation)) CPH_Program.verifier e1 e2 data2 slot)))) := by
  have original := Rc7_Native.accepted L sdk copy std allocator e1 e2 w1 w2
    admission1 admission2 c indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
    data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length
    prior words p t u actions game RuntimePersistence
  have strengthened := P2P_R6Result.strengthen L e1 e2 w1 w2
    (Rc5_Install.configuration indexError c reservation).adapter
    (Rc5_Install.configuration indexError c reservation).currentBase
    (Rc5_Install.configuration indexError c reservation).reserved
    (Rc5_Install.configuration indexError c reservation).query
    (Rc5_Install.configuration indexError c reservation).geometry
    (Rc5_Install.configuration indexError c reservation).stageBase
    (Rc5_Install.configuration indexError c reservation).finish c.boundaries reservation
    CPH_Program.verifier data1 data2 slot saved post1 post2 H
    (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
    (p.physicalEvents t) hashv native1 native2 extraction sha256 p1 syscall original
  exact P2P_Release.remove L e1 e2 w1 w2
    (Rc5_Install.configuration indexError c reservation).adapter
    (Rc5_Install.configuration indexError c reservation).currentBase
    (Rc5_Install.configuration indexError c reservation).reserved
    (Rc5_Install.configuration indexError c reservation).query
    (Rc5_Install.configuration indexError c reservation).geometry
    (Rc5_Install.configuration indexError c reservation).stageBase
    (Rc5_Install.configuration indexError c reservation).finish c.boundaries reservation
    CPH_Program.verifier data1 data2 slot saved post1 post2 H
    (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
    (p.physicalEvents t) hashv
    (SCE_Experiment.account (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a)
    project (Q0+Q1)
    (RawJ_CollisionBudget.first_reads
      (Rc5_Install.configuration indexError c reservation).adapter
      (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish
      (Rc5_Install.configuration indexError c reservation).reserved
      (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry
      (Rc5_Install.configuration indexError c reservation).boundaries
      (Rc5_Install.configuration indexError c reservation).std hashv copy allocator
      CPH_Program.verifier a.first a.second Q0 Q1 prefixBound choiceBound) strengthened

#print axioms accepted
end AspisR1.SCG_NativeAccount
end
