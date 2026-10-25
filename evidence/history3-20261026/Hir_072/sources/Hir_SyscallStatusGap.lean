import Hir_CallTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_SyscallStatusGap
open Aeneas Aeneas.Std Result SdkC_Source Hir_NoFault
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- An interface countermodel, NOT a shipped-source security finding: the
success-conditioned syscall contract permits an always-failing syscall.
It cannot silently justify the all-world experiment substitution. -/
theorem status_gap (sha256 : Bytes → State) (parts : Parts) :
    ∃ hashv : Parts → Result Digest,
      S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 ∧
      ¬ NoFault hashv (.read parts Code.done) ∧
      Hir_PartialOracle.program hashv (.read parts Code.done) ≠ SdkC_Oracle.program (.read parts Code.done) := by
  let hashv : Parts → Result Digest := fun _ => .fail .assertionFailure
  have syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 :=
    ⟨by intro input digest impossible; cases impossible⟩
  refine ⟨hashv,syscall,?_,?_⟩
  · intro safe
    obtain ⟨⟨digest,impossible⟩,_⟩ := safe
    cases impossible
  · intro equal
    have observed := congrArg (fun p => (eval (fun _ => (fun _ => 0)) p).1.length) equal
    change 0 = 1 at observed
    omega

#print axioms status_gap
end AspisR1.Hir_SyscallStatusGap
end
