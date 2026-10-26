import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_PartialOracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def partial : SdkC_Source.Parts → Result SdkC_Source.Digest := fun _ => .fail .assertionFailure

def code (parts : SdkC_Source.Parts) : SdkC_Source.Code Bool := .read parts (fun _ => .done true)

/-- The retained syscall law deliberately permits failures. -/
theorem syscall (H : Bytes → State) : S2W_ExtractionBoundary.RuntimeSyscall partial H := by
  constructor
  intro parts digest success
  cases success

/-- The accepted-native-to-ideal theorem cannot be reversed under merely the
retained returning-value law. A tiny code diagnostic, not an installed forgery. -/
theorem not_reverse (parts : SdkC_Source.Parts) (H : Bytes → State) :
    (eval H (SdkC_Oracle.program (code parts))).2 = .ok true ∧
    (SdkC_Source.run partial (code parts) []).1 = .fail .assertionFailure ∧
    S2W_ExtractionBoundary.RuntimeSyscall partial H :=
  ⟨rfl,rfl,syscall H⟩

#print axioms syscall
#print axioms not_reverse
end AspisR1.SCG_PartialOracle
end
