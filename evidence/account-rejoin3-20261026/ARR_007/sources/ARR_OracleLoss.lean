import ARR_OracleCoverage
import SCG_PartialOracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_OracleLoss
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- This is the literal source digest helper, not an installed accepted pair.
The retained RuntimeSyscall permits this partial dictionary. -/
theorem digest_loss (H : Bytes → State) (parts : SdkC_Source.Parts) :
    S2W_ExtractionBoundary.RuntimeSyscall SCG_PartialOracle.failingOracle H ∧
    S2W_ExtractionBoundary.P1 H H ∧
    (SdkC_Source.run SCG_PartialOracle.failingOracle (SdkC_Source.digestCode parts) []).1 ≠
      (eval H (SdkC_Oracle.program (SdkC_Source.digestCode parts))).2 := by
  refine ⟨SCG_PartialOracle.syscall H,SCG_PartialOracle.realization H,?_⟩
  intro same
  have impossible := (ARR_OracleCoverage.digest_iff H _ parts).mp same
  cases impossible

/-- An ideal continuation may issue calls after the native failing prefix.
This precise two-read diagnostic does NOT assert a deployed accepted attack. -/
def two (p q : SdkC_Source.Parts) : Code Bool :=
  .read p (fun _ => .read q (fun _ => .done true))

theorem cost_loss (H : Bytes → State) (p q : SdkC_Source.Parts) :
    (SdkC_Source.run SCG_PartialOracle.failingOracle (two p q) []).2.length = 1 ∧
    (eval H (SdkC_Oracle.program (two p q))).1.length = 2 ∧
    (SdkC_Source.run SCG_PartialOracle.failingOracle (two p q) []).1 = .fail .assertionFailure ∧
    (eval H (SdkC_Oracle.program (two p q))).2 = .ok true := by
  simp only [two,SdkC_Source.run,SCG_PartialOracle.failingOracle,
    SdkC_Oracle.program,eval,List.length_cons,List.length_nil]
  exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms digest_loss
#print axioms cost_loss
end AspisR1.ARR_OracleLoss
end
