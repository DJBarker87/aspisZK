import P6C_Extension
import Rc5_Top
import Rc6_Result
import Rc6_Install
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
namespace AspisR1.Rc6_Top
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
    (raw : F3T_CanonicalJoin.AcceptedVerifierJoin
      (Rc5_Install.configuration indexError c reservation) D
      (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv))
    (binding : F3T_Runtime.StoredCarrierBinding
      (Rc5_Install.configuration indexError c reservation) D
      (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv) P runtime)
    (adversary : Program Bytes State (GExq_AccountExperiment.FirstInputs A))
    (chooseSecond : GExq_AccountExperiment.FirstInputs A → alloc.vec.Vec U8 →
      Heap (Nat → Record) → A → Program Bytes State (GExq_AccountExperiment.SecondInputs A))
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (Rc5_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase (Rc5_Install.configuration indexError c reservation).stageBase
        (Rc5_Install.configuration indexError c reservation).finish (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query (Rc5_Install.configuration indexError c reservation).geometry
        (Rc5_Install.configuration indexError c reservation).boundaries (Rc5_Install.configuration indexError c reservation).std ∧
    (Rc6_Result.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv) ∧
    ((∀ H : Bytes → State,(eval H (annotatedWith D (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv)
        (F3T_Canon.canon (lift (Rc5_Install.configuration indexError c reservation) P)))).2.2=true →
      mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
        (view (eval H (annotatedWith D (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv) (F3T_Canon.canon (lift (Rc5_Install.configuration indexError c reservation) P))))) coins).2.total : Rat))≤
          ((CostedAllocationLedgerM10.params (Q0+Q1+1161)).attemptBudget : Rat)) ∧
    (∀ run coins w,(ActualCostedExtractorM10.extractor.eval run coins).1=some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:Rat)^126+1/(2:Rat)^454≤1/(2:Rat)^120) ∧
    (F3T_RuntimeBound.failureModel runtime≤StartChargeNumeric.totalBound (Q0+Q1)) ∧
    (Q0+Q1≤OraclePortHeadlineFrozen2.Qmax → F3T_RuntimeBound.failureModel runtime≤(Q0+Q1+1:Rat)*(1/(2:Rat)^100))) ∧
    (let r := Rc5_Install.configuration indexError c reservation;
      F3T_RuntimeBound.failureModel runtime +
        F3T_AccountCharge.mass (CPG_Account.source r hashv copy allocator CPH_Program.verifier adversary chooseSecond)
          project select (Q0+Q1) ≤ F3T_Numeric.total (Q0+Q1)) ∧
    (let r := Rc5_Install.configuration indexError c reservation;
      Q0+Q1 = 0 → F3T_RuntimeBound.failureModel runtime +
        F3T_AccountCharge.mass (CPG_Account.source r hashv copy allocator CPH_Program.verifier adversary chooseSecond)
          project select (Q0+Q1) < 1/(2:Rat)^100) ∧
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
  obtain ⟨driverEq,sdkEq,original,headline,bound,zero,copyFacts,events,protection,trace,recorder⟩ :=
    Rc5_Top.deployed L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
      native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
      D P Q0 Q1 queries runtime raw binding adversary chooseSecond prefixBound choiceBound project select
  refine ⟨P6C_Extension.boundary hashv sha256 H p1 syscall,driverEq,sdkEq,?_,headline,bound,zero,
    copyFacts,events,protection,trace,recorder⟩
  exact Rc6_Result.strengthen L e1 e2 w1 w2
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

#print axioms deployed
end AspisR1.Rc6_Top
end
