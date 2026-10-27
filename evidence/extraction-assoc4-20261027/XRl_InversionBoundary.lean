import XRk_ABI
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_InversionBoundary
/-- The supplied inversion model rejects zero rather than manufacturing a
successful inverse. Its field inverse/Fermat/source-P6 law remains OPEN. -/
theorem zero_rejected : aspis_core.field.M31.inv 0#u32=fail .panic := by rfl

theorem success (x y : aspis_core.field.M31) (run : aspis_core.field.M31.inv x=ok y) :
    x≠0#u32 ∧ XRk_mpow x 2147483645=ok y := by
  by_cases zero : x=0#u32
  · simp only [aspis_core.field.M31.inv,zero,↓reduceIte] at run
    cases run
  · exact ⟨zero,by simpa only [aspis_core.field.M31.inv,zero,↓reduceIte] using run⟩
#print axioms zero_rejected
#print axioms success
end XRl_InversionBoundary
