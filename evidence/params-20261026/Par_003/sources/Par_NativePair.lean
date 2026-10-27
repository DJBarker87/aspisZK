import DrvC_NativePair
import Par_Public
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Par_NativePair
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

open DrvC_Installation
open AspisV8R19.MemoizedProgramLaw
theorem accepted_pair {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (DrvC_FirstConstants.configuration c).currentBase) (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (DrvC_FirstConstants.configuration c).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (DrvC_FirstConstants.configuration c).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (DrvC_FirstConstants.configuration c).stageBase) (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry)) (DrvC_FirstConstants.configuration c).finish) (Uni_Install.current (DrvC_FirstConstants.configuration c).currentBase (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry) (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std) native1 native2 hashv)
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
 :
    ∃ (f : FirstCut) (s : SecondCut) (i : OraclePortStoredExperimentC4.Input),
      SourceCuts (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c))
        e1.first (e2.second secondSizes) saved f s ∧
      Port1_Driver.decodeSemantic (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c))
        f.pub = ok (some f.semantic) ∧
      i.statement.pubBytes = bytesOf f.pub.val ∧ i.stored = bytesOf f.proof.val ∧
      i.statement.tag = 2 ∧ i.statement.pubBytes.length = 1880 ∧
      75 + i.statement.pubBytes.length ≤ SelectedTranscriptParams.L ∧
      ∀ (history : S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val))
        (p2prime : P2Prime H f.proof f.pub s.proof s.pub),
        (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) i)).2 = true ∧
        ¬ (∀ j, (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) j)).2 = false) := by
  obtain ⟨f,s,cuts,decoded,accept⟩ := DrvC_NativePair.accepted_pair_driver L sdk copy std allocator
    e1 e2 w1 w2 admission1 admission2 c native1 native2 prepareOwner primitiveOwner hashv extraction
    sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2 saved post1 post2
    accepted1 accepted2 Par_Parameters.deployed root length
  have size := DrvC_PublicCarrier.public_length _ _ _ _ f s cuts
  let i := Par_Public.input f.pub f.proof size
  obtain ⟨pubSize,fit⟩ := Par_Public.accepted_public_bound _ _ _ _ f s cuts
  refine ⟨f,s,i,cuts,decoded,rfl,rfl,rfl,pubSize,fit,?_⟩
  intro history p2prime
  have yes := accept history p2prime i rfl rfl
  refine ⟨yes,?_⟩
  intro rejects
  have bad := (rejects i).symm.trans yes
  cases bad

#print axioms accepted_pair
#print accepted_pair
end AspisR1.Par_NativePair
end
