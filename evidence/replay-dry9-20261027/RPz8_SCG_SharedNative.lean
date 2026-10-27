import RPz8_SCG_NativeAccount
import RPz8_SCG_Selection
import RPz8_SCG_Recorder
import RPz8_SCE_NativeFirst
import RPz8_SCE_Experiment
import RPz8_Rc7_Native
import RPz8_P2P_Release
import RPz8_P2P_Accounting
import RPz8_FGl_Cost
import RPz8_Rc6_Result
import RPz7_P6C_Extension
import RPz8_F3Y_InstalledLaws
import RPz8_FGl_Bound
import RPz8_F3Y_SourceClaims
import RPz8_F3Y_AccountMass
import RPz8_F3X_ModelClaims
import RPz8_F3U_Range
import RPz7_Rc5_Source
import RPz7_Rc5_Close
import RPz7_Rc5_Install
import RPz7_CPH_Recorder
import RPz7_CPH_Trace
import CPH_Program
import RPz7_CPH_Pair
import RPz7_CPH_Protection
import RPz7_Rc2_Events
import RPz7_CPG_Pair
import RPz7_CPG_Account
import RPz7_CPP_Install
import RPz7_F3T_ConditionalClaims
import RPz7_CPG_History
import RPz7_CPR_PhysicalResult
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_Cons_Pair
import RPz7_Cons_Finish
import RPz7_Cons_Native
import RPz7_Cons_Continuation
import RPz7_Cons_Base
import RPz7_Cons_Caller
import RPz7_Cons_Result
import RPz7_T2R_FullResult
import RPz7_T2R_Pair
import RPz7_Par_Headline
import RPz7_Par_Transcript
import RPz7_Cons_NativeBuild
import RPz7_Cons_FinishProof
import RPz7_Cons_Second
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
namespace AspisR1.SCG_SharedNative
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
/-- Same native/game pointwise theorem with response-selected entries and one
fixed outcome-dependent selector. No all-world game assertion is introduced. -/
theorem accepted {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (a : SCE_Experiment.Adversary A) (w1 w2 : W)
    (c : DrvC_Installation.Configuration F CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (admission1 : RuntimeEntrypointAdmission L ((eval H a.first).2.entry) w1 3)
    (admission2 : RuntimeEntrypointAdmission L ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) w2 7)
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
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    P2P_Result.Outcome L ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier ((eval H a.first).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot) saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (SCE_Experiment.account (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier a)
          project (Hiq_ByteSelection.select (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation)) CPH_Program.verifier)))) := by
  have native := SCG_NativeAccount.accepted L sdk copy std allocator ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) w1 w2
    admission1 admission2 c indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
    ((eval H a.first).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot) ((eval H a.first).2.state) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.state) final1 final2 saved post1 post2 accepted1 accepted2 root length
    prior words p t u actions game RuntimePersistence a Q0 Q1 prefixBound choiceBound project
  let r := Rc5_Install.configuration indexError c reservation
  have first := SCE_NativeFirst.result r hashv allocator CPH_Program.verifier native1 native2
    extraction sha256 H p1 syscall copy (eval H a.first).2 saved post1 final1 accepted1
  have selected := SCG_Selection.actual r hashv copy allocator CPH_Program.verifier
    (DrvC_Installation.sdk r) a H saved post1 final1 first
  have same := SCG_Recorder.select_congr
    (SCE_Experiment.account r hashv copy allocator CPH_Program.verifier a) project
    (Hiq_ByteSelection.select (DrvC_Installation.sdk r) CPH_Program.verifier)
    (fun _ => P2P_NativeSelection.pair (DrvC_Installation.sdk r) CPH_Program.verifier ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot))
    H selected
  rw [← same] at native
  exact native

#print axioms accepted
end AspisR1.SCG_SharedNative
end
