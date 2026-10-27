import CPG_Pair
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
namespace AspisR1.CPG_Top
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

theorem deployed {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).currentBase) (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).reserved (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).query (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).geometry (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).boundaries (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).stageBase) (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).reserved (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).query (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).geometry)) (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).finish) (Uni_Install.current (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).currentBase (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).reserved (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).query (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).geometry) (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).boundaries (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).std) native1 native2 hashv)
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
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPG_Game.DeployedPairExecution p t u e1 e2 saved actions)
    (system : S2W_ExtractionBoundary.Program) (programNotSystem : program ≠ system)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system) (CPG_Projection.before p)
      (CPG_Projection.tentative p native1 native2 copy allocator program)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (runtime : F3T_Runtime.Runtime)
    (raw : F3T_CanonicalJoin.AcceptedVerifierJoin
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) D
      (F3T_Installed.source (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) hashv))
    (binding : F3T_Runtime.StoredCarrierBinding
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) D
      (F3T_Installed.source (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) hashv) P runtime) :
    (CPR_PhysicalResult.Outcome L e1 e2 w1 w2
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).adapter (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).currentBase
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).reserved (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).query
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).geometry (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).stageBase
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).finish (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).boundaries
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)).std program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (DrvC_FirstConstants.configuration (CPP_Install.configuration c))) prior
      (CPG_Projection.result p native1 native2 copy allocator program t).2) ∧
    (∀ H : Bytes → State,(eval H (annotatedWith D (F3T_Installed.source (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) hashv)
        (F3T_Canon.canon (lift (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) P)))).2.2=true →
      mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
        (view (eval H (annotatedWith D (F3T_Installed.source (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) hashv) (F3T_Canon.canon (lift (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) P))))) coins).2.total : Rat))≤
          ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat)) ∧
    (∀ run coins w,(ActualCostedExtractorM10.extractor.eval run coins).1=some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:Rat)^126+1/(2:Rat)^454≤1/(2:Rat)^120) ∧
    (F3T_RuntimeBound.failureModel runtime≤StartChargeNumeric.totalBound Q) ∧
    (Q≤OraclePortHeadlineFrozen2.Qmax → F3T_RuntimeBound.failureModel runtime≤(Q+1:Rat)*(1/(2:Rat)^100)) := by
  constructor
  · exact CPG_Pair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (CPP_Install.configuration c) native1 native2 prepareOwner primitiveOwner hashv extraction
      sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2 saved post1 post2
      accepted1 accepted2 root length prior p t u actions game system programNotSystem
      (CPP_Install.key c) RuntimePersistence
  · exact F3T_ConditionalClaims.claims
      (DrvC_FirstConstants.configuration (CPP_Install.configuration c)) D P Q queries hashv runtime raw binding

#print axioms deployed
end AspisR1.CPG_Top
end
