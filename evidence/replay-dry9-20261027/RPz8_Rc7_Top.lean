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
namespace AspisR1.Rc7_Top
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

/-- One native witness factory; one selected Q+2965 event for the frozen3
headline and P2Prime byte binding. Global finish owners and L159 remain. -/
theorem deployed {W A F CoreError Tx : Type}
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
    (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : F3T_Runtime.Runtime)
    (finishOwners : FGl_PreparedAt.Owners
      (Rc5_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation).boundaries)
    (binding : F3T_Runtime.StoredCarrierBinding
      (Rc5_Install.configuration indexError c reservation) D
      (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv) P runtime)
    :
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (Rc5_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase (Rc5_Install.configuration indexError c reservation).stageBase
        (Rc5_Install.configuration indexError c reservation).finish (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query (Rc5_Install.configuration indexError c reservation).geometry
        (Rc5_Install.configuration indexError c reservation).boundaries (Rc5_Install.configuration indexError c reservation).std ∧
    (P2P_Result.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (Rc5_Install.configuration indexError c reservation) hashv P)
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (Rc5_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (Rc5_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (Rc5_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc5_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (Rc5_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved := by
  dsimp only
  let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
    fun _ => P2P_NativeSelection.pair
      (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation))
      CPH_Program.verifier e1 e2 data2 slot
  have prepare := F3Y_InstalledLaws.prepare indexError c reservation
  have ports := F3Y_InstalledLaws.primitives indexError c reservation
  have canonical := F3Y_InstalledLaws.canonical indexError c reservation
  have domain := F3Y_InstalledLaws.domain indexError c reservation
  have multiply := F3Y_InstalledLaws.multiply indexError c reservation
  have one := F3Y_InstalledLaws.one indexError c reservation
  have inverse := F3Y_InstalledLaws.inverse indexError c reservation
  have security := FGl_Bound.bound
    (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation)
    hashv D words P (Q0+Q1) queries runtime select prepare ports canonical domain multiply one inverse
    finishOwners binding
  have sourceCost := FGl_Cost.source_cost
    (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation)
    hashv D words P (Q0+Q1) queries select prepare ports canonical domain multiply one inverse finishOwners
  have accountMass := F3Y_AccountMass.claims
    (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation)
    hashv D words P (Q0+Q1) queries select
  refine ⟨P6C_Extension.boundary hashv sha256 H p1 syscall,DrvC_SourceEntry.same_program (Rc3_Install.select (Rc5_Install.seed indexError c) reservation) hashv,
    DrvC_Installation.aus1_dictionary (Rc5_Install.configuration indexError c reservation),
    ?_,?_,?_,?_,?_,?_,?_⟩
  · have original := Rc7_Native.accepted L sdk copy std allocator e1 e2 w1 w2
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
      (F3X_Account.program (Rc5_Install.configuration indexError c reservation) hashv P)
      F3X_Projection.project (Q0+Q1)
      (F3Y_AccountMass.budget (Rc2_Install.configuration (Rc5_Install.seed indexError c) reservation)
        hashv D words P (Q0+Q1) queries) strengthened
  · refine ⟨F3X_ModelClaims.claims _ D P (Q0+Q1) queries,sourceCost,accountMass,security,?_,?_⟩
    · intro range
      simpa only [Nat.cast_add] using security.trans (F3U_Range.per_attempt _ range)
    · intro zero
      rw [zero] at security
      exact F3U_Numeric.runtime_margin _ security
  · exact PoolT_Write.accepted_verifier_writes_copy (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation)) native1 native2 hashv extraction copy std allocator
      e1 CPH_Program.verifier data1 state1 final1 saved post1 accepted1
  · exact Rc2_Events.derive _ hashv native1 native2 extraction copy allocator CPH_Program.verifier sha256 H p1 syscall saved
  · exact CPH_Protection.derive p t u e1 e2 saved actions (Rc5_Install.configuration indexError c reservation)
      (Rc5_Install.key indexError c reservation) native1 native2 hashv extraction copy std allocator CPH_Program.verifier game
      data1 state1 final1 post1 accepted1
  · exact CPH_Trace.derive game
  · exact CPH_Recorder.physical p t u e1 e2 saved actions (Rc5_Install.configuration indexError c reservation)
      native1 native2 hashv extraction copy allocator CPH_Program.verifier game sha256 H p1 syscall

#print axioms deployed
end AspisR1.Rc7_Top
end
