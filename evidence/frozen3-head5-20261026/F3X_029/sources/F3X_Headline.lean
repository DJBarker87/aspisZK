import F3X_Native
import F3X_Bound
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
namespace AspisR1.F3X_Headline
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

theorem deployed {W A F CoreError : Type}
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
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : F3T_Runtime.Runtime)
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives (F3X_Installation.configuration c reservation).geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain (F3X_Installation.configuration c reservation).geometry)
    (multiply : (F3X_Installation.configuration c reservation).geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : (F3X_Installation.configuration c reservation).geometry.op7=ok (1#u32))
    (inverse : (F3X_Installation.configuration c reservation).geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : F3X_PreparedAt.Owners (F3X_Installation.configuration c reservation)
      (Rc2_Install.configuration c reservation).boundaries)
    (L159_StoredCarrierBinding : F3T_Runtime.StoredCarrierBinding
      (F3X_Installation.configuration c reservation) D
      (F3T_Installed.source (F3X_Installation.configuration c reservation) hashv) P runtime)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    DrvC_Implementation.driver (F3X_Installation.configuration c reservation) =
      DrvC_SourceEntry.source (F3X_Installation.configuration c reservation) hashv ∧
    DrvC_Installation.sdk (F3X_Installation.configuration c reservation) =
      SdkD_PairBatches.dictionary (F3X_Installation.configuration c reservation).adapter
        (F3X_Installation.configuration c reservation).currentBase (F3X_Installation.configuration c reservation).stageBase
        (F3X_Installation.configuration c reservation).finish (F3X_Installation.configuration c reservation).reserved
        (F3X_Installation.configuration c reservation).query (F3X_Installation.configuration c reservation).geometry
        (F3X_Installation.configuration c reservation).boundaries (F3X_Installation.configuration c reservation).std ∧
    (F3T_RuntimeBound.failureModel runtime≤F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1≤F3U_RangeEdges.maxQueries → F3T_RuntimeBound.failureModel runtime≤(Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin≤1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime<1/(2:Rat)^100)) ∧
    (Rc2_Result.Outcome L e1 e2 w1 w2 (F3X_Installation.configuration c reservation).adapter (F3X_Installation.configuration c reservation).currentBase (F3X_Installation.configuration c reservation).reserved (F3X_Installation.configuration c reservation).query (F3X_Installation.configuration c reservation).geometry (F3X_Installation.configuration c reservation).stageBase (F3X_Installation.configuration c reservation).finish (F3X_Installation.configuration c reservation).boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (F3X_Installation.configuration c reservation)) prior (F3X_Installation.configuration c reservation) hashv native1 native2 copy allocator) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (F3X_Installation.configuration c reservation) hashv native1 native2 copy allocator program H saved ∧
    Rc2_Protection.Facts (F3X_Installation.configuration c reservation) native1 native2 copy allocator program := by
  obtain ⟨driverEq,sdkEq,original,copyFacts,eventFacts,protectionFacts⟩ := F3X_Native.accepted
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    (F3V_Install.configuration c) reservation native1 native2 prepareOwner primitiveOwner hashv extraction
    sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2 saved post1 post2
    accepted1 accepted2 root length prior
  have security := F3X_Bound.bound (Rc2_Install.configuration c reservation) hashv D w P (Q0+Q1)
    hqueries runtime select prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse
    finishOwners L159_StoredCarrierBinding
  refine ⟨driverEq,sdkEq,⟨security,?_,?_⟩,original,copyFacts,eventFacts,protectionFacts⟩
  · intro range
    simpa only [Nat.cast_add] using security.trans (F3U_Range.per_attempt _ range)
  · intro zero
    rw [zero] at security
    exact F3U_Numeric.runtime_margin _ security

#print axioms deployed
end AspisR1.F3X_Headline
end
