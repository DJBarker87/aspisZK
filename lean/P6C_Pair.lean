import P6C_Extension
import SdkC_BatchPair
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Pair
open Aeneas Aeneas.Std Result SdkC_Source
open S2W_NativeConsolidation S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2Trust
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- A derived accepted-run output; it is never an input hypothesis. -/
def Safe {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A) : Prop :=
  SdkC_BatchPair.Returning hashv H code value ∧
  (∀ q ∈ (run hashv code []).2, ∃ digest,
    q.returned = ok digest ∧ hashv q.parts = ok digest) ∧
  run (fun parts => ok (P6C_Extension.total hashv H parts)) code [] = run hashv code []

theorem safe {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A) (returned : SdkC_BatchPair.Returning hashv H code value) :
    Safe hashv H code value :=
  ⟨returned,P6C_Accepted.actual_calls_ok hashv code value returned.1,
    P6C_Extension.source_preserved hashv H code [] value returned.1⟩

/-- Both installed batches, with the SAME native accepted wrappers/cuts and
source-computed logs. Every issued call returns, and the total extension
preserves all source results and attempts in their original order. -/
theorem accepted_pair_calls {A F : Type}
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
        Safe hashv H (SdkC_BatchSource.currentCode hashv f.proof p0 root0) (.Ok ()) ∧
        Safe hashv H (SdkC_BatchSource.stageCode hashv s.proof p2 root2) (.Ok ()) := by
  obtain ⟨f,s,cuts,unchanged,p0,root0,p2,root2,firstSafe,secondSafe⟩ :=
    SdkC_BatchPair.accepted_pair copy stdCopy allocator e1 e2 adapter ops stage finish B std
      native1 native2 hashv extraction sha256 H p1 syscall program data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
  exact ⟨f,s,cuts,unchanged,p0,root0,p2,root2,
    safe hashv H _ _ firstSafe,safe hashv H _ _ secondSafe⟩

#print axioms safe
#print axioms accepted_pair_calls
end AspisR1.P6C_Pair
end
