import RPz7_DrvC_CutAcceptance
import RPz7_CPhy_Physical
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.DrvC_NativePair
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
theorem accepted_pair_driver {W A M Cv F CoreError : Type} {N : Nat}
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
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
 :
    ∃ f s,
      SourceCuts (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)) e1.first (e2.second secondSizes) saved f s ∧
      Port1_Driver.decodeSemantic (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)) f.pub = ok (some f.semantic) ∧
      ∀ (history : S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val))
        (p2prime : P2Prime H f.proof f.pub s.proof s.pub)
        (i : OraclePortStoredExperimentC4.Input),
        i.statement.pubBytes = bytesOf f.pub.val → i.stored = bytesOf f.proof.val →
        (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) i)).2 = true := by
  let r := DrvC_FirstConstants.configuration c
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,writer,reader,rest⟩ :=
    CPhy_Physical.accepted_pair_unified L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      r.adapter r.currentBase r.reserved r.query r.geometry (AuS1_Install.base r.stageBase)
      r.finish r.boundaries r.std native1 native2 prepareOwner primitiveOwner hashv extraction
      sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2 saved post1 post2
      accepted1 accepted2 p root length
  obtain ⟨owned1,written⟩ := first_accepted native1 copy std allocator e1 program data1 state1 final1 saved post1 accepted1
  have source1 : AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk r) program e1.first data1 = ok (.Ok saved) :=
    (extraction.stage1 program e1.first data1).symm.trans owned1
  obtain ⟨semantic,decoded,newcuts⟩ := DrvC_DecodeCut.same_cut r program e1.first (e2.second secondSizes)
    data1 saved f s source1 cuts
  refine ⟨{f with semantic := semantic},s,newcuts,decoded,?_⟩
  intro history p2prime i publicCarrier proofCarrier
  have destinationSize := checkpoint_size e1 (DrvC_Installation.sdk r) program data1 saved source1
  have versionAtWrite : S2X.CheckpointVersionBinding
      (payloadBytes encode ((writeBracket e1.heap 2 0 0 (source (nativeBytes saved))).payload
        (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) := by
    rw [← written]; exact history
  obtain ⟨_,⟨version⟩⟩ := returned_committed e1.heap 2 0 0 saved (bytesOf s.checkpoint.val)
    rfl rfl destinationSize (writer.size saved cuts.first) versionAtWrite
  obtain ⟨sameProof,samePub,sameCheckpoint,size⟩ := S2W_AuthenticatedInputs.authenticated_inputs
    (DrvC_Installation.sdk r) CPhy_Header.decode H f.semantic f.pub f.proof s.pub s.proof s.checkpoint
    f.split saved cuts.first cuts.second writer reader version p2prime
  exact DrvC_CutAcceptance.driver_accepts c native1 native2 hashv extraction sha256 H p1 syscall
    e1.first (e2.second secondSizes) saved {f with semantic := semantic} s newcuts decoded
    sameProof samePub sameCheckpoint i publicCarrier proofCarrier

#print axioms accepted_pair_driver
#print accepted_pair_driver
end AspisR1.DrvC_NativePair
end
