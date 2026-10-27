import XSd_InverseShape
import SAQ_Inverse
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_InverseCompare
theorem kit_two : aspis_core.field.M31.inv 2#u32=ok 2#u32 := by
 rw [XSd_InverseShape.inverse_spine _ (by decide)]
 rfl
theorem cohort_two : ∃ y, AspisR1.SAQ_Inverse.source 2#u32=ok y ∧ y≠2#u32 := by
 have hn : R17CurrentM31Semantics.decode 2#u32 ≠ 0 := by decide
 obtain ⟨y,hy,hv⟩ := AspisR1M31Inverse.SquareProof.current_inv_total_inverse 2#u32 hn
 refine ⟨y,hy,?_⟩
 intro same
 subst y
 have hi := inv_mul_cancel₀ hn
 rw [←hv] at hi
 norm_num [R17CurrentM31Semantics.decode] at hi
 have bad := congrArg ZMod.val hi
 have no : ZMod.val (4 : ZMod 2147483647) ≠ ZMod.val (1 : ZMod 2147483647) := by decide
 exact no bad

theorem mismatch : aspis_core.field.M31.inv 2#u32 ≠ AspisR1.SAQ_Inverse.source 2#u32 := by
 obtain ⟨y,hy,ne⟩ := cohort_two
 rw [kit_two,hy]
 intro same
 exact ne (Result.ok.inj same).symm

/-- Both sides succeed; this is a value mismatch, not vacuous rejection. -/
theorem both_success : ∃ y, aspis_core.field.M31.inv 2#u32=ok 2#u32 ∧
 AspisR1.SAQ_Inverse.source 2#u32=ok y ∧ y≠2#u32 := by
 obtain ⟨y,hy,ne⟩ := cohort_two
 exact ⟨y,kit_two,hy,ne⟩
#print axioms kit_two
#print axioms cohort_two
#print axioms mismatch
#print axioms both_success
end XSd_InverseCompare
