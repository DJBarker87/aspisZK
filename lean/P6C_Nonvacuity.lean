import P6C_Extension
import P6B_Totality
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open P6B_Totality

/-- Existing success-only runtime trust admits a partial syscall. The new
mathematical gates and a genuine accepted source call hold nevertheless. -/
theorem partial_accepted (H : Bytes → State) :
    S2W_ExtractionBoundary.P1 H H ∧
    S2W_ExtractionBoundary.RuntimeSyscall (partialHash H) H ∧
    ¬ Returns (partialHash H) ∧
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary (partialHash H) H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    (run (partialHash H) (digestCode emptyParts) []).1 =
      ok (MultiproofConePhysicalTransport.rawOracle H emptyParts) ∧
    run (fun parts => ok (P6C_Extension.total (partialHash H) H parts)) (digestCode emptyParts) [] =
      run (partialHash H) (digestCode emptyParts) [] := by
  have p1 : S2W_ExtractionBoundary.P1 H H := ⟨fun _ => rfl⟩
  have runtime := partial_runtime H
  have accepted : (run (partialHash H) (digestCode emptyParts) []).1 =
      ok (MultiproofConePhysicalTransport.rawOracle H emptyParts) := by
    rw [digest_trace,partial_success]
  exact ⟨p1,runtime,partial_not_total H,
    P6C_Extension.boundary (partialHash H) H H p1 runtime,accepted,
    P6C_Extension.source_preserved (partialHash H) H _ [] _ accepted⟩

/-- Off the accepted class the extension genuinely changes execution.
The accepted-run condition has not silently been dropped. -/
theorem rejected_differs (H : Bytes → State) :
    run (fun parts => ok (P6C_Extension.total (partialHash H) H parts)) (digestCode onePart) [] ≠
      run (partialHash H) (digestCode onePart) [] := by
  rw [digest_trace,digest_trace]
  intro same
  have value := congrArg Prod.fst same
  simp only [partialHash,onePart,List.cons_ne_nil,if_false] at value
  cases value

#print axioms partial_accepted
#print axioms rejected_differs
end AspisR1.P6C_Nonvacuity
end
