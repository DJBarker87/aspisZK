import LPk_Cohort
import ExtractedQM31SamplerPassLoop
set_option autoImplicit false
namespace NDH_Qm31Pass
open Aeneas Aeneas.Std Result ControlFlow

theorem loop_eq (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop rank r j =
      AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop rank r j := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop
  congr 1
  funext x
  rcases x with ⟨a,r,j⟩
  exact LPk_Cohort.body_eq a r j

theorem pass_eq (rank : Array U32 8#usize) :
    AspisR1Post25Sampler.sampler.qm31_div_pass rank =
      AspisR1Qm31SamplerIndex.sampler.qm31_div_pass rank := by
  simp only [AspisR1Post25Sampler.sampler.qm31_div_pass,
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass, loop_eq]

#print axioms loop_eq
#print axioms pass_eq
end NDH_Qm31Pass
