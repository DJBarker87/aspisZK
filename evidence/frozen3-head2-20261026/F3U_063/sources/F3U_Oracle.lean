import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Oracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def hashv (H : Bytes → State) (parts : SdkC_Source.Parts) : Result SdkC_Source.Digest :=
  ok (encodeState (H (flatten parts)))

theorem decoded (H : Bytes → State) (parts : SdkC_Source.Parts) :
    decodeState (encodeState (H (flatten parts)))=H (flatten parts) := by
  exact state_roundtrip _

theorem syscall (H : Bytes → State) : S2W_ExtractionBoundary.RuntimeSyscall (hashv H) H := by
  constructor
  intro parts digest returned
  have eq : encodeState (H (flatten parts))=digest := Result.ok.inj returned
  rw [←eq]
  exact decoded H parts

#print axioms decoded
#print axioms syscall
end AspisR1.F3U_Oracle
end
