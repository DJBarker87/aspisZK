import Rc2_Top
import PFin_Result
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
namespace AspisR1.PFin_Top
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
      (Tx1Q_Execution.actual (Op5T_Concrete.current (Rc2_Install.configuration c reservation).currentBase) (Rc2_Install.configuration c reservation).reserved (Rc2_Install.configuration c reservation).query (Rc2_Install.configuration c reservation).geometry (Rc2_Install.configuration c reservation).boundaries (Rc2_Install.configuration c reservation).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (Rc2_Install.configuration c reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (Rc2_Install.configuration c reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (Rc2_Install.configuration c reservation).stageBase) (Rc2_Install.configuration c reservation).reserved (Rc2_Install.configuration c reservation).query (Rc2_Install.configuration c reservation).geometry)) (Rc2_Install.configuration c reservation).finish) (Uni_Install.current (Rc2_Install.configuration c reservation).currentBase (Rc2_Install.configuration c reservation).reserved (Rc2_Install.configuration c reservation).query (Rc2_Install.configuration c reservation).geometry) (Rc2_Install.configuration c reservation).boundaries (Rc2_Install.configuration c reservation).std) native1 native2 hashv)
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
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (Rc2_Install.configuration c reservation) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (Rc2_Install.configuration c reservation) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    DrvC_Implementation.driver (Rc2_Install.configuration c reservation) =
      DrvC_SourceEntry.source (Rc2_Install.configuration c reservation) hashv ∧
    DrvC_Installation.sdk (Rc2_Install.configuration c reservation) =
      SdkD_PairBatches.dictionary (Rc2_Install.configuration c reservation).adapter
        (Rc2_Install.configuration c reservation).currentBase (Rc2_Install.configuration c reservation).stageBase
        (Rc2_Install.configuration c reservation).finish (Rc2_Install.configuration c reservation).reserved
        (Rc2_Install.configuration c reservation).query (Rc2_Install.configuration c reservation).geometry
        (Rc2_Install.configuration c reservation).boundaries (Rc2_Install.configuration c reservation).std ∧
    (let r := Rc2_Install.configuration c reservation
    let source := GExp_Experiment.program
      (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
      (DrvC_Installation.stage r) r.reserved r.boundaries r.std hashv
      (DrvC_Installation.currentDigest r) (DrvC_Installation.digest r) adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100)) ∧
    (PFin_Result.Outcome L e1 e2 w1 w2 (Rc2_Install.configuration c reservation).adapter (Rc2_Install.configuration c reservation).currentBase (Rc2_Install.configuration c reservation).reserved (Rc2_Install.configuration c reservation).query (Rc2_Install.configuration c reservation).geometry (Rc2_Install.configuration c reservation).stageBase (Rc2_Install.configuration c reservation).finish (Rc2_Install.configuration c reservation).boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc2_Install.configuration c reservation)) prior (Rc2_Install.configuration c reservation) hashv native1 native2 copy allocator) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc2_Install.configuration c reservation) hashv native1 native2 copy allocator program H saved ∧
    Rc2_Protection.Facts (Rc2_Install.configuration c reservation) native1 native2 copy allocator program := by
  obtain ⟨driverEq,sdkEq,headline,original,copyFacts,events,protection⟩ := Rc2_Top.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c reservation native1 native2
    prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    D P Q0 Q1 hqueries runtime raw binding adversary chooseSecond prefixBound choiceBound project
  refine ⟨driverEq,sdkEq,headline,?_,copyFacts,events,protection⟩
  exact PFin_Result.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ _ reservation program
    data1 data2 slot saved post1 post2 H _ prior _ hashv native1 native2 copy allocator
    extraction sha256 p1 syscall original

#print axioms deployed
end AspisR1.PFin_Top
end
