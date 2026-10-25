import Hir_CallSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CallLog
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers GExq_AccountExperiment Hir_Call
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def attempts (store : Store) (call : Call A) : SdkC_Source.Log :=
  match Hiq_ReleaseRoute.route call.data with
  | .first => (SdkC_Source.run hashv (firstCode c hashv copy allocator id store call) []).2
  | .second => (SdkC_Source.run hashv (secondCode c hashv allocator id store call) []).2
  | .reject => []

theorem exact_log (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (store : Store) (call : Call A) :
    (eval H (oracle c hashv copy allocator id store call)).1 =
      SdkC_Source.readLog (attempts c hashv copy allocator id store call) := by
  unfold oracle attempts
  cases route : Hiq_ReleaseRoute.route call.data with
  | reject => rfl
  | first =>
    simp only [eval_bind,eval,List.append_nil]
    exact (Hir_PartialOracle.exact hashv sha256 H p1 syscall _ []).2.symm
  | second =>
    simp only [eval_bind,eval,List.append_nil]
    exact (Hir_PartialOracle.exact hashv sha256 H p1 syscall _ []).2.symm

#print axioms exact_log
end AspisR1.Hir_CallLog
end
