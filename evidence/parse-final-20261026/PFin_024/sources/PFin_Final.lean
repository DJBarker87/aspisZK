import PFin_FinalResult
import PFin_SelectedPair
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
namespace AspisR1.PFin_Final
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

theorem accepted {W A F CoreError : Type}
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
 :
    PFin_FinalResult.Outcome L e1 e2 w1 w2 (Rc2_Install.configuration c reservation).adapter (Rc2_Install.configuration c reservation).currentBase (Rc2_Install.configuration c reservation).reserved (Rc2_Install.configuration c reservation).query (Rc2_Install.configuration c reservation).geometry (Rc2_Install.configuration c reservation).stageBase (Rc2_Install.configuration c reservation).finish (Rc2_Install.configuration c reservation).boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc2_Install.configuration c reservation)) prior (Rc2_Install.configuration c reservation) hashv native1 native2 copy allocator := by
  let r := Rc2_Install.configuration c reservation
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,selected,publicFacts,caller⟩ :=
    PFin_SelectedPair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      r.adapter r.currentBase r.reserved r.query r.geometry r.stageBase r.finish r.boundaries r.std
      native1 native2 prepareOwner primitiveOwner hashv extraction prior sha256 H p1 syscall program data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 Par_Parameters.deployed root length
  have ⟨cuts,writer,reader,multi,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
  have sourceFacts := T2R_Parser.on_run _ _ _ _ _ _ _ _ _ _ _ _ _ run header1.2.2.1 scanned.2.2
  have strong := Rc2_Base.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ _ reservation program
    data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run base
  have initial := NP6_Constructors.on_run _ _ _ _ _ _ _ _ _ _ _ run
  have accepted := T2R_Nonvacuity.same_cuts L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (Rc2_Install.select c reservation) native1 native2 prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
      f s cuts writer reader
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,strong,initial,publicFacts,sourceFacts,accepted,?_⟩
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary r.adapter r.currentBase r.stageBase r.finish r.reserved r.query r.geometry r.boundaries r.std)
      e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact cuts
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary r.adapter r.currentBase r.stageBase r.finish r.reserved r.query r.geometry r.boundaries r.std)
      native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  exact PFin_BoundCaller.from_cut L e1 e2 w1 w2 r.adapter r.currentBase r.reserved r.query r.geometry
    r.stageBase r.finish r.boundaries r.std program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2
    pairCuts selected header1.2.2.1 scanned.2.2 native1 native2 hashv pairExtraction sha256 p1 syscall caller

#print axioms accepted
end AspisR1.PFin_Final
end
