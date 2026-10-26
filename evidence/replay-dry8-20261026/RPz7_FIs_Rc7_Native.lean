/- FIs same-run enrichment; read-only source: Rc7_Native.lean. -/
import RPz7_FIs_P2P_R5Result
import RPz7_FIs_P2P_R5Close
import RPz7_FIs_P2P_Source
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
import RPz7_FIs_Cons_Second
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
namespace AspisR1.FIs_Rc7_Native
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

/-- Composed adopted frozen3 endpoint on the owner-approved two-transaction checkpoint
projection. RuntimePersistence is the named external runtime item. The system
program is the fixed all-zero public key; the verifier identity is selected from the
retained exact-default-ELF deployment receipt. The raw canonical join, runtime carrier
binding, P2Prime and FirstEntry are retained. -/
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
 :
    (FIs_P2P_R5Result.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t)) := by
  obtain ⟨_,_,source,_,_⟩ := FIs_P2P_Source.source L sdk copy std allocator e1 e2 w1 w2
    admission1 admission2 (Rc5_Install.seed indexError c) reservation native1 native2
    (SAQ_Decoder.primitives c.query) hashv extraction sha256 H p1 syscall
    CPH_Program.verifier data1 data2 slot state1 state2 final1 final2 saved post1 post2
    accepted1 accepted2 root length prior words
  exact FIs_P2P_R5Close.from_saf L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    c indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
    CPH_Program.verifier data1 data2 slot state1 state2 final1 final2 saved post1 post2
    accepted1 accepted2 root length prior p t u actions game (Hist_Nonvacuity.key 0#u8)
    CPH_Program.not_system RuntimePersistence source

#print axioms accepted
end AspisR1.FIs_Rc7_Native
end
