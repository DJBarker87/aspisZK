import ART_QueryCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_SyscallObstruction
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- Even choosing sha256 := H cannot repair NativeAt: its RuntimeSyscall
record constrains EVERY returning call, including an unissued address. -/
theorem no_native_world (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native : Bytes → State) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (parts : SdkC_Source.Parts) (digest : SdkC_Source.Digest)
    (returned : hashv parts = ok digest) (value : State)
    (different : value ≠ native (flatten parts)) :
    ¬ ∃ sha256, S2W_ExtractionBoundary.P1 sha256 (ART_QueryCylinder.change native (flatten parts) value) ∧
      S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 := by
  rintro ⟨sha256,p1,newSyscall⟩
  have old := syscall.returningValue parts digest returned
  have fresh := (newSyscall.returningValue parts digest returned).trans (p1.realization (flatten parts))
  simp only [ART_QueryCylinder.change,if_pos rfl] at fresh
  exact different (fresh.symm.trans old)

#print axioms no_native_world
end AspisR1.ART_SyscallObstruction
end
