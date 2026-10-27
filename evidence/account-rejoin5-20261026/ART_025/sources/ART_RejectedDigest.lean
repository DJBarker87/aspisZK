import ART_PartialExact
import RPx_FailedQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_RejectedDigest
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.SqueezeOracleBridge

theorem failed {A : Type} (parts : Parts) (k : Digest → Code A) (error : Error) (H : Bytes → State) :
    eval H (ART_PartialProgram.program (fun _ => .fail error) (.read parts k) []) =
      ([(flatten parts,H (flatten parts))],(.fail error,[⟨parts,.fail error⟩])) := by
  rfl

theorem diverged {A : Type} (parts : Parts) (k : Digest → Code A) (H : Bytes → State) :
    eval H (ART_PartialProgram.program (fun _ => .div) (.read parts k) []) =
      ([(flatten parts,H (flatten parts))],(.div,[⟨parts,.div⟩])) := by
  rfl

/-- The failed native call consumes one original attempt even when the
corresponding ideal successful continuation would issue arbitrarily more. -/
theorem stopped (H : Bytes → State) (p q : Parts) :
    (eval H (ART_PartialProgram.program SCG_PartialOracle.failingOracle (ARR_OracleLoss.two p q) [])).1.length = 1 ∧
    (eval H (ART_PartialProgram.program SCG_PartialOracle.failingOracle (ARR_OracleLoss.two p q) [])).2.1 = .fail .assertionFailure ∧
    (eval H (SdkC_Oracle.program (ARR_OracleLoss.two p q))).1.length = 2 := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms failed
#print axioms diverged
#print axioms stopped
end AspisR1.ART_RejectedDigest
end
