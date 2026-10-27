import CurrentWideQMMulM31V5
set_option autoImplicit false
namespace AspisR1.SAG_MScaleTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem total (x scalar : field.M31) : ∃ out, field.M31.mul x scalar = ok out := by
  obtain ⟨out,run,_,_⟩ := ExtractedCurrentReducer.current_mul_mod x scalar
  exact ⟨out,by rw [m31_mul_same]; exact run⟩

#print axioms total
end AspisR1.SAG_MScaleTotal
