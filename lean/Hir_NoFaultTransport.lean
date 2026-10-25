import Hir_NoFault
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_NoFaultTransport
open Aeneas Aeneas.Std Result SdkC_Source Hir_NoFault
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Literal PROGRAM equality, stronger than acceptance/byte equality or a
single-world log comparison. This transports every probability law without
conditioning on native success. The NoFault source instance stays explicit. -/
theorem program_eq (hashv : Parts → Result Digest) {A : Type} (code : Code A)
    (safe : NoFault hashv code) : Hir_PartialOracle.program hashv code = SdkC_Oracle.program code := by
  induction code with
  | done value => rfl
  | step result k ih => cases result with
    | ok value => exact ih value safe
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    obtain ⟨⟨digest,actual⟩,all⟩ := safe
    simp only [Hir_PartialOracle.program,SdkC_Oracle.program,actual]
    congr 1
    funext answer
    exact ih (encodeState answer) (all _)

theorem every_outcome (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    {A : Type} (code : Code A) (safe : NoFault hashv code) :
    eval H (SdkC_Oracle.program code) =
      (readLog (run hashv code []).2,(run hashv code []).1) := by
  rw [← program_eq hashv code safe]
  obtain ⟨result,log⟩ := Hir_PartialOracle.exact hashv sha256 H p1 syscall code []
  exact Prod.ext log.symm result

#print axioms program_eq
#print axioms every_outcome
end AspisR1.Hir_NoFaultTransport
end
