import NNH_HostExec
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_DigestProgramStatus
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
/-- Fixed syntax: the interpreter reads only the syscall's status. This is
one component of O1; it makes no account-syntax or dictionary claim. -/
theorem total_status {A : Type} (h1 h2 : Parts → Result Digest)
 (ok1 : ∀ parts, ∃ d, h1 parts = .ok d) (ok2 : ∀ parts, ∃ d, h2 parts = .ok d)
 (code : Code A) (before : Log) :
 ART_PartialProgram.program h1 code before = ART_PartialProgram.program h2 code before := by
 induction code generalizing before with
 | done a => rfl
 | step r k ih =>
  cases r with
  | ok a => exact ih a before
  | fail e => rfl
  | div => rfl
 | read parts k ih =>
  obtain ⟨d1,e1⟩ := ok1 parts
  obtain ⟨d2,e2⟩ := ok2 parts
  simp only [ART_PartialProgram.program,e1,e2]
  congr 1
  funext value
  exact ih _ _

theorem adapter_fixed {A : Type} (sha256 : Bytes → State) (d0 : Digest)
 (code : Code A) (before : Log) :
 ART_PartialProgram.program (DGP_HostDigest.hashvInst sha256) code before =
 ART_PartialProgram.program (fun _ => .ok d0) code before :=
 total_status _ _ (fun _ => ⟨_,rfl⟩) (fun _ => ⟨_,rfl⟩) code before
#print axioms total_status
#print axioms adapter_fixed
end AspisR1.NNH_DigestProgramStatus
end
