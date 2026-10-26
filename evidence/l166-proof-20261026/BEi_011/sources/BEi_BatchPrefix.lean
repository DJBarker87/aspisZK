import BEi_BatchCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_BatchPrefix
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Consumer interface for an operationally associated batch cut. All
quantifiers, the physical-cut history argument, and the local relation remain
visible. It is not an axiom or an adopted physical-runtime law. -/
theorem export_cut {S A : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : Code A) (n : Nat) (count : GExp_CountLaws.count n code)
    (state after : S) (before log : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    log = before ++ BEi_RecorderCut.issued before log ∧
    BEi_RecorderCut.issued before log = (SdkC_Source.run hashv code []).2 ∧
    (BEi_RecorderCut.issued before log).length ≤ n ∧
    ∃ remaining,
      (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
        RPx_AttemptPrefix.addresses (BEi_RecorderCut.issued before log) ++ remaining := by
  have exactCut := BEi_RecorderCut.source_cut call hashv binding code state after before log value execution
  refine ⟨(BEi_RecorderCut.exact_cut call code state after before log value execution).1,
    exactCut,?_,?_⟩
  · rw [exactCut]
    simpa only [List.length_nil,Nat.zero_add] using
      GExp_PartialCount.from_count code n count hashv sha256 H p1 syscall []
  · obtain ⟨kept,remaining,same,ideal⟩ := RPx_AttemptPrefix.transport code hashv sha256 H p1 syscall []
    simp only [RPx_AttemptPrefix.addresses,List.map_nil,List.nil_append] at same
    exact ⟨remaining,by rw [exactCut,same];exact ideal⟩

#print axioms export_cut
end AspisR1.BEi_BatchPrefix
end
