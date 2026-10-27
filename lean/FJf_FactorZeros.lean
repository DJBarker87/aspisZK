import FJf_FactorArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_FactorZeros
open Aeneas Aeneas.Std Result

def zeros : FJf_PointBody.Factors := Array.repeat 5#usize
  (Array.repeat 5#usize (Array.repeat 4#usize FIn_WeightsExtract.field.QM31.ZERO))

theorem canon : FJf_FactorArray.canon zeros := by
  intro r hr
  simp only [zeros,Array.repeat,List.mem_replicate] at hr
  rcases hr with ⟨_,rfl⟩
  intro d hd
  simp only [Array.repeat,List.mem_replicate] at hd
  rcases hd with ⟨_,rfl⟩
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩
  exact FJc_WeightConstants.zero.1
#print axioms canon
end AspisR1.FJf_FactorZeros
end
