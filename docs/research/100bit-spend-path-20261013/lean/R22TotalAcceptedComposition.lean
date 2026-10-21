import R22TotalCoreCones
import ExtractedCurrentQM31Exact

/-! A concrete upstream domain discharge. Canonicality is obtained from actual
sampler totality, not assumed from acceptance of a wrapping execution. This
constructed typed pipeline is not identified with a frozen caller here. -/
set_option autoImplicit false
namespace AspisR1.R22TotalAcceptedComposition
open Aeneas Aeneas.Std Result R22TotalCheckedComposition
open ExtractedQM31SamplerCarrier
abbrev Block := Array U8 32#usize

def sampledProduct (input : Block × Block) : Result CurrentQM := do
  let x ← AspisR1Qm31SamplerIndex.sampler.qm31_sample input.1
  let y ← AspisR1Qm31SamplerIndex.sampler.qm31_sample input.2
  AspisR1Qm31ArithmeticProbe.field.QM31.mul (toCurrent x) (toCurrent y)

theorem sampledProduct_total (input : Block × Block) :
    ∃ z, sampledProduct input = ok z ∧ CurrentCanonicalQM z := by
  obtain ⟨x, hx, hcx, _⟩ := ExtractedQM31SamplerCorrect.sample_total input.1
  obtain ⟨y, hy, hcy, _⟩ := ExtractedQM31SamplerCorrect.sample_total input.2
  obtain ⟨z, hz, hcz, _⟩ :=
    ExtractedCurrentQM31Exact.current_qm_mul_exact (toCurrent x) (toCurrent y) hcx hcy
  refine ⟨z, ?_, hcz⟩
  simp only [sampledProduct, hx, hy, bind_tc_ok, hz]

theorem sampledProduct_R22 (t : Translation sampledProduct) : R22TotalCoreCones.ConeR22 t := by
  apply extracted_total_R22
  intro input
  obtain ⟨z, hz, _⟩ := sampledProduct_total input
  exact ⟨z, hz⟩

#print axioms sampledProduct_total
#print axioms sampledProduct_R22
end AspisR1.R22TotalAcceptedComposition
