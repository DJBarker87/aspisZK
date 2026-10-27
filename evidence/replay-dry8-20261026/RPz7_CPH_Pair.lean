import RPz7_CPH_Rc2Source
import RPz7_CPH_Close
import RPz7_CPH_Game
import RPz7_CPH_Install
import RPz7_CPH_Result
import RPz7_CPG_History
import RPz7_CPR_PhysicalResult
import RPz7_CPG_Result
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
namespace AspisR1.CPH_Pair
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

theorem accepted {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (input : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (CPH_Install.configuration input reservation).currentBase) (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query (CPH_Install.configuration input reservation).geometry (CPH_Install.configuration input reservation).boundaries (CPH_Install.configuration input reservation).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (CPH_Install.configuration input reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (CPH_Install.configuration input reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (CPH_Install.configuration input reservation).stageBase) (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query (CPH_Install.configuration input reservation).geometry)) (CPH_Install.configuration input reservation).finish) (Uni_Install.current (CPH_Install.configuration input reservation).currentBase (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query (CPH_Install.configuration input reservation).geometry) (CPH_Install.configuration input reservation).boundaries (CPH_Install.configuration input reservation).std) native1 native2 hashv)
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
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator program)
    (system : S2W_ExtractionBoundary.Program) (programNotSystem : program ≠ system)
    (keyLaw : (DrvC_Installation.sdk (CPH_Install.configuration input reservation)).op36 = Hist_Authority.keyEq)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p)) :
    CPH_Result.Outcome L e1 e2 w1 w2
      (CPH_Install.configuration input reservation).adapter (CPH_Install.configuration input reservation).currentBase
      (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query
      (CPH_Install.configuration input reservation).geometry (CPH_Install.configuration input reservation).stageBase
      (CPH_Install.configuration input reservation).finish (CPH_Install.configuration input reservation).boundaries
      reservation program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (CPH_Install.configuration input reservation)) prior (CPH_Install.configuration input reservation) hashv native1 native2 copy allocator
      (p.physicalEvents t) := by
  obtain ⟨driverEq,sdkEq,original,copied,events,protection⟩ := CPH_Rc2Source.source
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 (CPP_Install.configuration input) reservation
    native1 native2 prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
  exact CPH_Close.from_rc2 L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    input reservation native1 native2 prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall
    program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length
    prior p t u actions game system programNotSystem keyLaw RuntimePersistence original

#print axioms accepted
end AspisR1.CPH_Pair
end
