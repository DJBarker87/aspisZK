import SAG_WScaleTotal
import SAG_StageScale
set_option autoImplicit false
noncomputable section
attribute [local irreducible] QuadraticAlgebra.instInv
namespace AspisR1.SAG_ScaleNonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

theorem total (claim : E) (scalar : M) : ∃ rhs, SAG_StageScale.mulM claim scalar = ok rhs := by
  obtain ⟨actual,run⟩ := SAG_WScaleTotal.total (SAQ_WideABI.toW claim) scalar
  exact ⟨SAQ_WideABI.fromW actual,by simp only [SAG_StageScale.mulM,run,bind_tc_ok]⟩

/-- Every raw claim has an actual successful installed quarter multiply;
the discharged law is not true merely because its success guard is empty. -/
theorem quarter {W : Type} (seed : FinishOps W) (claim : E) :
    ∃ rhs, (SAG_StageScale.install seed).quarter = ok 536870912#u32 ∧
      (SAG_StageScale.install seed).mulM claim 536870912#u32 = ok rhs ∧
      CheckpointBytes5Output.ofE rhs = RoundPairing.quarter * CheckpointBytes5Output.ofE claim := by
  obtain ⟨rhs,run⟩ := total claim 536870912#u32
  exact ⟨rhs,rfl,run,SAG_StageScale.quarter seed _ claim rhs rfl run⟩

#print axioms total
#print axioms quarter
end AspisR1.SAG_ScaleNonvacuity
end
