import Par_NativePair
import RowOrder_History
import DrvC_CutAcceptance
import CPhy_Physical
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.T2R_Nonvacuity
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
theorem same_cuts {W A F CoreError : Type}
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
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c))
      e1.first (e2.second secondSizes) saved f s)
    (writer : CheckpointWriterConeJoin (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c))
      CPhy_Header.decode H f.semantic f.pub f.proof f.split)
    (reader : CheckpointReaderConeJoin (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c))
      CPhy_Header.decode H s.pub s.proof s.checkpoint) :
    ∃ i : OraclePortStoredExperimentC4.Input,
      i.statement.pubBytes = bytesOf f.pub.val ∧ i.stored = bytesOf f.proof.val ∧
      i.statement.tag = 2 ∧ i.statement.pubBytes.length = 1880 ∧
      75 + i.statement.pubBytes.length ≤ SelectedTranscriptParams.L ∧
      ∀ (history : S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val))
        (p2prime : P2Prime H f.proof f.pub s.proof s.pub),
        (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) i)).2 = true ∧
        ¬ (∀ j, (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) j)).2 = false) := by
  let r := DrvC_FirstConstants.configuration c
  obtain ⟨owned1,written⟩ := first_accepted native1 copy std allocator e1 program data1 state1 final1 saved post1 accepted1
  have source1 : AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk r)
      program e1.first data1 = ok (.Ok saved) :=
    (extraction.stage1 program e1.first data1).symm.trans owned1
  obtain ⟨semantic,decoded,newcuts⟩ := DrvC_DecodeCut.same_cut r program e1.first (e2.second secondSizes)
    data1 saved f s source1 cuts
  have size := DrvC_PublicCarrier.public_length r e1.first (e2.second secondSizes) saved f s cuts
  let i := Par_Public.input f.pub f.proof size
  obtain ⟨pubSize,fit⟩ := Par_Public.accepted_public_bound r e1.first (e2.second secondSizes) saved f s cuts
  refine ⟨i,rfl,rfl,rfl,pubSize,fit,?_⟩
  intro history p2prime
  obtain ⟨version,key,ledger,events,sameCheckpoint,sameProof,samePub,savedLength⟩ :=
    RowOrder_History.on_d189_cuts copy std allocator e1 e2 _ native1 native2 hashv extraction
      program data1 state1 final1 saved post1 accepted1 f s cuts CPhy_Header.decode H writer reader history p2prime
  have yes := DrvC_CutAcceptance.driver_accepts c native1 native2 hashv extraction sha256 H p1 syscall
    e1.first (e2.second secondSizes) saved {f with semantic := semantic} s newcuts decoded
    sameProof samePub sameCheckpoint i rfl rfl
  refine ⟨yes,?_⟩
  intro rejects
  cases (rejects i).symm.trans yes

#print axioms same_cuts
end AspisR1.T2R_Nonvacuity
end
