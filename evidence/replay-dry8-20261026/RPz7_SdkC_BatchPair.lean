import RPz7_SdkC_BatchSource
import RPz7_Op5T_SamePair
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_BatchPair
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2Trust
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- An OUTPUT of source acceptance. All log occurrences are computed; none
is an independently supplied execution, erased port, or successful child. -/
def Returning {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H : Bytes → State) (code : SdkC_Source.Code A) (value : A) : Prop :=
  (SdkC_Source.run hashv code []).1 = .ok value ∧
  eval H (SdkC_Oracle.program code) =
    (SdkC_Source.readLog (SdkC_Source.run hashv code []).2,.ok value) ∧
  ∀ a d, d ≠ H a → (a,d) ∉ SdkC_Source.readLog (SdkC_Source.run hashv code []).2

theorem returning {A : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : SdkC_Source.Code A) (value : A)
    (success : (SdkC_Source.run hashv code []).1 = .ok value) : Returning hashv H code value :=
  ⟨success,SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall code value success,
    fun a d bad => SdkC_Source.no_fabricated_reply hashv sha256 H p1 syscall code a d bad⟩

/-- Both complete installed source bodies on THE SAME cuts. The arbitrary
SDK child is not used to select either log or to justify any hash reply. -/
theorem same_pair {F : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (Op5T_SamePair.dictionary adapter ops stage finish B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (Op5T_SamePair.dictionary adapter ops stage finish B std) accounts1 accounts2 saved f s) :
    ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
      (p2 : VTop_Stages.verifier.Prepared) (root2 : Array U8 32#usize),
      Returning hashv H (SdkC_BatchSource.currentCode hashv f.proof p0 root0) (.Ok ()) ∧
      Returning hashv H (SdkC_BatchSource.stageCode hashv s.proof p2 root2) (.Ok ()) := by
  obtain ⟨p0,root0,p2,root2,batch0,batch2⟩ :=
    Op5T_SamePair.batches adapter ops stage finish B std accounts1 accounts2 saved f s cuts
  have binding := S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction
  refine ⟨p0,root0,p2,root2,?_,?_⟩
  · apply returning hashv sha256 H p1 syscall
    exact (SdkC_BatchSource.current_source hashv _ (binding ()) f.proof p0 root0 []).trans batch0
  · apply returning hashv sha256 H p1 syscall
    exact (SdkC_BatchSource.stage_source hashv _ (binding ()) s.proof p2 root2 []).trans batch2

/-- Accepted native wrappers supply the actual cut pair and both source logs.
This is a batch-source theorem, not the complete Op5T_Final schedule theorem. -/
theorem accepted_pair {A F : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (stdCopy : TrustedStd copy) (allocator : Allocator A) (e1 e2 : Entry)
    (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (Op5T_SamePair.dictionary adapter ops stage finish B std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator e1 program data1 state1 = .ok (.Ok (saved,post1,final1)))
    (accepted2 : second native2 allocator e2 program data2 slot state2 = .ok (.Ok (post2,final2))) :
    ∃ f s,
      SourceCuts (Op5T_SamePair.dictionary adapter ops stage finish B std)
        e1.first (e2.second secondSizes) saved f s ∧
      post2 = e2.heap ∧
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
        (p2 : VTop_Stages.verifier.Prepared) (root2 : Array U8 32#usize),
        Returning hashv H (SdkC_BatchSource.currentCode hashv f.proof p0 root0) (.Ok ()) ∧
        Returning hashv H (SdkC_BatchSource.stageCode hashv s.proof p2 root2) (.Ok ()) := by
  obtain ⟨owned1,_⟩ := first_accepted native1 copy stdCopy allocator e1 program data1 state1 final1 saved post1 accepted1
  obtain ⟨owned2,unchanged⟩ := second_accepted native2 allocator e2 program data2 slot state2 final2 post2 accepted2
  obtain ⟨f,s,cuts⟩ := cuts_of_acceptance _ native1 native2 hashv
    (S2W_DigestExtraction.sourceBoundary _ native1 native2 hashv extraction)
    program e1.first (e2.second secondSizes) data1 data2 slot saved owned1 owned2
  exact ⟨f,s,cuts,unchanged,same_pair adapter ops stage finish B std native1 native2 hashv
    extraction sha256 H p1 syscall _ _ saved f s cuts⟩

#print axioms returning
#print axioms same_pair
#print axioms accepted_pair
#print accepted_pair
end AspisR1.SdkC_BatchPair
end
