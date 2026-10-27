import BEj_ReifiedBatch
import BEi_BatchPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEj_LocalExport
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Conditional consumer of the approved weak local law. No operational
execution, rejected final-state equality, or free successful log is required.
The local law itself MUST still be proved at the reached physical boundary. -/
theorem cut {S A E F : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (code : Code (core.result.Result A F)) (state : S) (before : Log)
    (native : BEh_Scope.Outcome S A E)
    (law : BEh_Scope.Law native (BEf_Carrier.run call code state before)) :
    native.2.2 = before ++ BEi_RecorderCut.issued before native.2.2 ∧
    BEi_RecorderCut.issued before native.2.2 = (SdkC_Source.run hashv code []).2 ∧
    (∀ a, native.1 = .ok (.Ok a) →
      native.2.1 = (BEf_Carrier.run call code state before).2.1) := by
  have logs := BEh_Scope.logs _ _ law
  have steps := BEi_ExecutionComplete.complete call code state before
  obtain ⟨prefix,_⟩ := BEi_RecorderCut.exact_cut call code state _ before _ _ steps
  have source := BEi_RecorderCut.source_cut call hashv binding code state _ before _ _ steps
  refine ⟨?_,?_,fun a h => congrArg Prod.fst (law.1.2 a h)⟩
  · rw [logs]; exact prefix
  · rw [logs]; exact source

/-- Conditional chronological prefix for ARR. The native endpoint is the
same supplied cut, and every outcome is retained. This is not its admission. -/
theorem prefix {S A E F : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : Code (core.result.Result A F)) (n : Nat) (count : GExp_CountLaws.count n code)
    (state : S) (before : Log) (native : BEh_Scope.Outcome S A E)
    (law : BEh_Scope.Law native (BEf_Carrier.run call code state before)) :
    native.2.2 = before ++ BEi_RecorderCut.issued before native.2.2 ∧
    BEi_RecorderCut.issued before native.2.2 = (SdkC_Source.run hashv code []).2 ∧
    (BEi_RecorderCut.issued before native.2.2).length ≤ n ∧
    ∃ remaining,
      (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
        RPx_AttemptPrefix.addresses (BEi_RecorderCut.issued before native.2.2) ++ remaining := by
  have logs := BEh_Scope.logs _ _ law
  rw [logs]
  exact BEi_BatchPrefix.export_cut call hashv binding sha256 H p1 syscall code n count
    state _ before _ _ (BEi_ExecutionComplete.complete call code state before)

#print axioms cut
#print axioms prefix
end AspisR1.BEj_LocalExport
end
